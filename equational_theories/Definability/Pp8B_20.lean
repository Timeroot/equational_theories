import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation1921 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq275 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq383 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq275 X0 X1
       grind)
    | exact superpose eq275 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275 (σ y) (σ x)
       grind)
    | exact superpose eq275 eq16
    | (have j1 := eq275 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq393 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq389
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq389
    | exact resolve eq389 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq395 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq392 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq392 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq392 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq421 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq395 X1 (τ X0)
       grind)
    | exact superpose eq395 eq17
    | (have j1 := eq395 X1 (τ X0)
       grind)
    | exact resolve eq17 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq427 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq395 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq421 X1 (τ X0)
       grind)
    | exact superpose eq421 eq18
    | (have j1 := eq421 X1 (τ X0)
       grind)
    | exact resolve eq18 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq421
  have eq763 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq758 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq758
    | (have j0 := eq758 X0 X1
       grind)
    | exact resolve eq758 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq777 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq763 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq763
    | (have j0 := eq763 X0 X1
       grind)
    | exact resolve eq763 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq780 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq777
    | (have j0 := eq777 X0 X1
       grind)
    | exact resolve eq777 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq838 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq780 X0 X1
       have i₂ := eq395 X0 X1
       grind)
    | exact superpose eq395 eq780
    | (have j0 := eq780 X1 X0
       have j1 := eq395 X1 X0
       grind)
    | exact resolve eq780 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq780
  have eq899 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq838 X0 X1
       have j1 := eq427 X0 X1
       grind)
    | (have r₁ := eq838 X0 X1
       have r₂ := eq427 X0 X1
       grind)
    | exact resolve eq838 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq838
  have eq938 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq899 X1 (σ X0)
       grind)
    | exact superpose eq899 eq22
    | (have j1 := eq899 X1 (σ X0)
       grind)
    | exact resolve eq22 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq899
  have eq975 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq938 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq938
    | (have j0 := eq938 X0 X1
       grind)
    | exact resolve eq938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq995 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq975 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq975
    | (have j0 := eq975 X0 X1
       grind)
    | exact resolve eq975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1256 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq995 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq995
    | exact resolve eq995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1256 x y
       grind)
    | exact superpose eq1256 eq16
    | (have j1 := eq1256 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1256 x y
       grind)
    | exact resolve eq16 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1340 : y = (k x y) := by grind
  clear eq1318
  have eq1536 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq393
       have i₂ := eq275 y x
       grind)
    | exact superpose eq275 eq393
    | (have j1 := eq275 y x
       grind)
    | exact resolve eq393 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1538 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1536
  have eq1539 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1538
       have i₂ := eq1340
       grind)
    | exact superpose eq1340 eq1538
    | exact resolve eq1538 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1540 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1539
       have i₂ := eq1340
       grind)
    | exact superpose eq1340 eq1539
    | exact resolve eq1539 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539
  have eq1542 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq393
       have i₂ := eq1540
       grind)
    | exact superpose eq1540 eq393
    | exact resolve eq393 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq1540
  have eq1555 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1542
  have eq1556 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1555
       have i₂ := eq1340
       grind)
    | exact superpose eq1340 eq1555
    | exact resolve eq1555 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1557 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1556
  have eq1561 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1557
       grind)
    | exact superpose eq1557 eq16
    | exact resolve eq16 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq1596 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1561
       have i₂ := eq275 y x
       grind)
    | exact superpose eq275 eq1561
    | (have j1 := eq275 y x
       grind)
    | exact resolve eq1561 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq1598 : (M.op x y) = (k x y) := by grind
  clear eq1596
  have eq1600 : y = (M.op x y) := by
    first
    | (have i₁ := eq1598
       have i₂ := eq1340
       grind)
    | exact superpose eq1340 eq1598
    | exact resolve eq1598 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq1598
  have eq1602 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1561
       have i₂ := eq1600
       grind)
    | exact superpose eq1600 eq1561
    | exact resolve eq1561 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561 eq1600
  have eq1617 : False := by grind
  exact eq1617

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1921 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq58 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq24
  have eq59 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58
    | (have j0 := eq58 X0
       grind)
    | exact resolve eq58 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq87 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq54 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq54 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq54 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq196 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq371 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq401 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq684 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq196
       have i₂ := eq401 x y
       grind)
    | exact superpose eq401 eq196
    | (have j1 := eq401 (σ x) (σ y)
       grind)
    | (have r₁ := eq196
       have r₂ := eq401 x y
       grind)
    | (have r₁ := eq196
       have r₂ := eq401 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq196
       have r₂ := eq401 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq196 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq401
  have eq685 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq684
  have eq687 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq704 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq687 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq687
    | (have j0 := eq687 X0
       grind)
    | exact resolve eq687 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq687
  have eq707 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq704 X0
       grind)
    | exact superpose eq704 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq704 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq704 X0
       grind)
    | exact resolve eq12 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq712 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq707 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq798 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq712 X0 X1
       grind)
    | exact superpose eq712 eq11
    | (have j1 := eq712 X0 X1
       grind)
    | exact resolve eq11 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq810 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq798 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq798
    | (have j0 := eq798 X0 X0
       grind)
    | exact resolve eq798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq854 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq810 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq855 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq923 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq855 X0
       grind)
    | exact superpose eq855 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq924 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq855 X0
       grind)
    | exact superpose eq855 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq939 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq855 (σ X0)
       grind)
    | exact superpose eq855 eq15
    | exact resolve eq15 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq939 X0
       have i₂ := eq855 X0
       grind)
    | exact superpose eq855 eq939
    | exact resolve eq939 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq939
  have eq14259 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq685
       grind)
    | exact superpose eq685 eq16
    | exact resolve eq16 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq14260 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq14259
       have r₂ := eq958 x
       grind)
    | exact resolve eq14259 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14259
  have eq14261 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14260
       have i₂ := eq958 y
       grind)
    | exact superpose eq958 eq14260
    | exact resolve eq14260 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14260
  have eq14263 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14261
       grind)
    | exact superpose eq14261 eq10
    | exact resolve eq10 eq14261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14261
  have eq14359 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14263
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14263
    | exact resolve eq14263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14263
  have eq14585 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14359
       grind)
    | exact superpose eq14359 eq16
    | exact resolve eq16 eq14359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14359
  have eq14586 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq14585
       have r₂ := eq958 x
       grind)
    | exact resolve eq14585 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14585
  have eq14596 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq923 y
       have i₂ := eq14586
       grind)
    | exact superpose eq14586 eq923
    | (have j0 := eq923 y
       grind)
    | (have r₁ := eq923 y
       have r₂ := eq14586
       grind)
    | exact resolve eq923 eq14586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14597 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq924 y X0
       have i₂ := eq14586
       grind)
    | exact superpose eq14586 eq924
    | (have j0 := eq924 y X0
       grind)
    | (have r₁ := eq924 y x
       have r₂ := eq14586
       grind)
    | exact resolve eq924 eq14586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14586
  have eq14621 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq14597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14597
  have eq14622 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq14596
  have eq14629 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq14621 X0
       have j1 := eq924 y X0
       grind)
    | (have r₁ := eq14621 X0
       have r₂ := eq924 y x
       grind)
    | exact resolve eq14621 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq14621
  have eq14630 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq923 y
       grind)
    | (have r₁ := eq14622
       have r₂ := eq923 y
       grind)
    | exact resolve eq14622 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq14622
  have eq14634 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq14630
       have i₂ := eq958 y
       grind)
    | exact superpose eq958 eq14630
    | exact resolve eq14630 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq14630
  have eq14729 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq14634
       grind)
    | exact superpose eq14634 eq10
    | exact resolve eq10 eq14634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14634
  have eq14833 : y = (M.op y y) := by
    first
    | (have i₁ := eq14729
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14729
    | exact resolve eq14729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14729
  have eq14874 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq14833
       grind)
    | exact superpose eq14833 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq14833
       grind)
    | exact resolve eq12 eq14833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14833
  have eq14907 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq14874 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14874
  have eq15161 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq14629 (σ X0)
       grind)
    | exact superpose eq14629 eq15
    | exact resolve eq15 eq14629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14629
  have eq15227 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15161 X0
       have i₂ := eq14907 X0
       grind)
    | exact superpose eq14907 eq15161
    | exact resolve eq15161 eq14907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907 eq15161
  have eq15798 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15227 x
       grind)
    | exact superpose eq15227 eq16
    | (have r₁ := eq16
       have r₂ := eq15227 x
       grind)
    | exact resolve eq16 eq15227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15227
  have eq15854 : False := by grind
  exact eq15854

/-- `Equation194`: `x = (y ◇ z) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation194 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law194 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law194.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X0 := by
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
  have eq37 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x y)) := by
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
  have eq38 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq46 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq61 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq93 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq133 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq46 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46
    | (have j0 := eq46 x
       grind)
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq143 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq133
       grind)
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq527 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq517 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq529 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq527 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq527 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq527 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq527 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq533 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq529
    | (have j0 := eq529 X0 X1
       grind)
    | exact resolve eq529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq8923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq120 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq8924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq8923
    | exact resolve eq8923 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8923
  have eq8935 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq8924
       have r₂ := eq27
       grind)
    | exact resolve eq8924 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8924
  have eq8937 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq8935
    | exact resolve eq8935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8935
  have eq8947 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq8937 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8937
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8937
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8937
       grind)
    | exact resolve eq13 eq8937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8937
  have eq8964 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq8947
  have eq9811 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq8964 eq117
    | exact resolve eq117 eq8964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq8964
  have eq9839 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq9811
    | exact resolve eq9811 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9811
  have eq9842 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq9839
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq9839
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq9839
       have r₂ := eq13 x y
       grind)
    | exact resolve eq9839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9839
  have eq9851 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq9842
       grind)
    | exact superpose eq9842 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq9842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9855 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq524 x y
       have i₂ := eq9842
       grind)
    | exact superpose eq9842 eq524
    | (have j0 := eq524 x y
       grind)
    | exact resolve eq524 eq9842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9842
  have eq9860 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9855
  have eq9861 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9851
  have eq9865 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9860
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9860
    | exact resolve eq9860 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9860
  have eq9869 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9861
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9861
    | exact resolve eq9861 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9861
  have eq9870 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9869
  have eq9882 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9865
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9865
    | exact resolve eq9865 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9865
  have eq9888 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9882
    | exact resolve eq9882 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9882
  have eq9889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq9888
  have eq9895 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9889
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9889
    | exact resolve eq9889 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9889
  have eq9902 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9895
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9895
    | exact resolve eq9895 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9895
  have eq9918 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq9870
       grind)
    | exact superpose eq9870 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9870
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9870
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9870
       grind)
    | exact resolve eq12 eq9870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9870
  have eq9938 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9918
  have eq9944 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9938
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9938
    | exact resolve eq9938 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9938
  have eq9945 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9944
  have eq9946 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9945
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9945
    | exact resolve eq9945 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9945
  have eq10590 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9902 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9902
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9902
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9902
       grind)
    | exact resolve eq12 eq9902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9902
  have eq10610 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10590
  have eq10616 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10610
    | exact resolve eq10610 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10610
  have eq10617 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq10616
  have eq10618 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10617
    | exact resolve eq10617 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10617
  have eq10777 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq9946
       grind)
    | exact superpose eq9946 eq133
    | exact resolve eq133 eq9946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq9946
  have eq10805 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10777
    | exact resolve eq10777 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10777
  have eq11223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10805 eq10618
    | exact resolve eq10618 eq10805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10618 eq10805
  have eq11232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11223
  have eq11234 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11232
       have r₂ := eq27
       grind)
    | exact resolve eq11232 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11232
  have eq11249 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11234 eq64
    | (have r₁ := eq64
       have r₂ := eq11234
       grind)
    | exact resolve eq64 eq11234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq11234
  have eq11259 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11249
  have eq11496 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11259 eq143
    | exact resolve eq143 eq11259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq11259
  have eq11529 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq11496
    | exact resolve eq11496 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11496
  have eq11531 : x = (k y x) := by
    first
    | (have r₁ := eq11529
       have r₂ := eq61
       grind)
    | exact resolve eq11529 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq11529
  have eq11767 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11531
       grind)
    | exact superpose eq11531 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11772 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq524 y x
       have i₂ := eq11531
       grind)
    | exact superpose eq11531 eq524
    | (have j0 := eq524 y x
       grind)
    | exact resolve eq524 eq11531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq11774 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq533 y x
       have i₂ := eq11531
       grind)
    | exact superpose eq11531 eq533
    | (have j0 := eq533 y x
       grind)
    | exact resolve eq533 eq11531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq11775 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11774
  have eq11777 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11772
  have eq11778 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq11767
  have eq11780 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11775
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11775
    | exact resolve eq11775 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11775
  have eq11782 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11777
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11777
    | exact resolve eq11777 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11777
  have eq11787 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11778
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11778
    | exact resolve eq11778 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11778
  have eq11796 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11780
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11780
    | exact resolve eq11780 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11780
  have eq11798 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11782
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11782
    | exact resolve eq11782 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11782
  have eq11803 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11796
    | exact resolve eq11796 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11796
  have eq11805 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq11798
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11798
    | exact resolve eq11798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11798
  have eq11810 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11803
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11803
    | exact resolve eq11803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11803
  have eq11812 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq11805
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11805
    | exact resolve eq11805 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11805
  have eq11817 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11810
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11810
    | exact resolve eq11810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11810
  have eq11819 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11812
    | exact resolve eq11812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11812
  have eq11824 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11817
    | exact resolve eq11817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11817
  have eq11866 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11824 eq27
    | exact resolve eq27 eq11824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11824
  have eq12194 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11787
       grind)
    | exact superpose eq11787 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11787
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11787
       grind)
    | exact resolve eq12 eq11787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12217 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq12194
  have eq12223 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12217
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12217
    | exact resolve eq12217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12217
  have eq12224 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq12223
  have eq12225 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12224
       have i₂ := eq11531
       grind)
    | exact superpose eq11531 eq12224
    | exact resolve eq12224 eq11531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11531 eq12224
  have eq12226 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12225
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12225
    | exact resolve eq12225 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq12225
  have eq12227 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12226 eq20
    | exact resolve eq20 eq12226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12226
  have eq12345 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12227
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12227
    | exact resolve eq12227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12227
  have eq12431 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12345 eq11866
    | (have r₁ := eq11866
       have r₂ := eq12345
       grind)
    | exact resolve eq11866 eq12345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12433 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12431
  have eq12543 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12433 eq27
    | exact resolve eq27 eq12433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12603 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12345 eq11819
    | exact resolve eq11819 eq12345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11819
  have eq12644 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12603
       have r₂ := eq27
       grind)
    | exact resolve eq12603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12603
  have eq13997 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12644 eq38
    | exact resolve eq38 eq12644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14209 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12433 eq13997
    | exact resolve eq13997 eq12433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13997
  have eq14230 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14209
  have eq14301 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14230 eq38
    | exact resolve eq38 eq14230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq14230
  have eq14487 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12433 eq14301
    | exact resolve eq14301 eq12433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12433 eq14301
  have eq14513 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14487
  have eq14667 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12345 eq14513
    | exact resolve eq14513 eq12345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12345 eq14513
  have eq14699 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14667
  have eq15041 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14699 eq12644
    | exact resolve eq12644 eq14699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12644 eq14699
  have eq15062 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq15041
  have eq15064 : x = (M.op x y) := by
    first
    | (have r₁ := eq15062
       have r₂ := eq12543
       grind)
    | exact resolve eq15062 eq12543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12543 eq15062
  have eq15067 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15064 eq20
    | exact resolve eq20 eq15064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq15069 : ∀ X0 : G, y = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq15064 eq37
    | exact resolve eq37 eq15064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq15183 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15067
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15067
    | exact resolve eq15067 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15067
  have eq15699 : y = (M.op y x) := by
    first
    | (have i₁ := eq15069 (M.op x x)
       have i₂ := eq15069 x
       grind)
    | exact superpose eq15069 eq15069
    | exact resolve eq15069 eq15069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15069
  have eq15752 : x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11787
       have i₂ := eq15699
       grind)
    | exact superpose eq15699 eq11787
    | exact resolve eq11787 eq15699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11787 eq15699
  have eq15792 : x = y ∨ x = y := by
    first
    | exact superpose eq15064 eq15752
    | exact resolve eq15752 eq15064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15064 eq15752
  have eq15793 : x = y := by grind
  clear eq15792
  have eq15901 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15793
       grind)
    | exact superpose eq15793 eq24
    | exact resolve eq24 eq15793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15793
  have eq16029 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15901
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15901
    | exact resolve eq15901 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15901
  have eq16083 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15183 eq16029
    | exact resolve eq16029 eq15183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029
  have eq16199 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16083 eq11866
    | (have r₁ := eq11866
       have r₂ := eq16083
       grind)
    | exact resolve eq11866 eq16083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11866 eq16083
  have eq16209 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16199
  have eq16212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15183 eq16209
    | exact resolve eq16209 eq15183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15183 eq16209
  have eq16280 : False := by grind
  exact eq16280

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxx_y_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X1)) X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq36 (τ X0)
       grind)
    | exact superpose eq36 eq18
    | exact resolve eq18 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq42 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq39
    | exact resolve eq39 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq42
    | exact resolve eq42 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq42
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
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
  clear eq17
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq44 X1
       grind)
    | exact superpose eq44 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq10
    | exact resolve eq10 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq133 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) ≠ X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = (k X1 (M.op (M.op X1 (M.op X2 X2)) X0)) ∨ (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = (M.op (M.op (M.op X1 (M.op X2 X2)) X0) (M.op (M.op X1 (M.op X2 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op (M.op X1 (M.op X2 X2)) X0)
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 X1 (M.op (M.op X1 (M.op X2 X2)) X0)
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ (τ (M.op X0 X0)))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142 (τ X0) X1 X2
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq142
    | exact resolve eq142 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq480 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq93 x y
       grind)
    | exact superpose eq93 eq16
    | (have j1 := eq93 x y
       grind)
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq530 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (M.op X0 X0)))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq296 (M.op x (τ (τ (M.op X0 X0)))) X1 X3
       have i₂ := eq296 X0 x (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq296 eq296
    | exact resolve eq296 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (τ (τ (M.op X1 X1)))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X1 (σ X0) (σ X0)
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq296
    | exact resolve eq296 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (M.op X0 X0))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq142 (M.op x (τ (τ (M.op X0 X0)))) X1 X3
       have i₂ := eq296 X0 x (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq296 eq142
    | exact resolve eq142 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1041 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (M.op X0 X0))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq296 (M.op x (τ (τ (τ (M.op X0 X0))))) X1 X3
       have i₂ := eq565 X0 x (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq565 eq296
    | exact resolve eq296 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq1700 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1740 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1700 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1700
    | (have j0 := eq1700 X0 X1
       grind)
    | exact resolve eq1700 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq2515 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq530 (M.op x (τ (τ (τ (τ (M.op X0 X0)))))) X1 X3
       have i₂ := eq530 X0 x (τ (τ (τ (τ (M.op X0 X0)))))
       grind)
    | exact superpose eq530 eq530
    | exact resolve eq530 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2596 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq565 (M.op x (τ (τ (τ (τ (M.op X0 X0)))))) X1 X3
       have i₂ := eq530 X0 x (τ (τ (τ (τ (M.op X0 X0)))))
       grind)
    | exact superpose eq530 eq565
    | exact resolve eq565 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq2660 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq480
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq480
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq2661 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq2660
  have eq5831 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X1 (M.op x (τ (τ (τ (τ (M.op X0 X0))))))
       have i₂ := eq530 X0 x (τ (τ (τ (τ (M.op X0 X0)))))
       grind)
    | exact superpose eq530 eq548
    | exact resolve eq548 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq7153 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq530 (M.op x (τ (τ (τ (τ (τ (M.op X0 X0))))))) X1 X3
       have i₂ := eq1041 X0 x (τ (τ (τ (τ (τ (M.op X0 X0))))))
       grind)
    | exact superpose eq1041 eq530
    | exact resolve eq530 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq1041
  have eq69685 : y ≠ y ∨ y = (k x y) ∨ (M.op y y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2661
       grind)
    | exact superpose eq2661 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2661
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2661
       grind)
    | exact resolve eq13 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661
  have eq69705 : y ≠ y ∨ y = (k x y) ∨ (M.op y y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by grind
  clear eq69685
  have eq69706 : y = (k x y) ∨ (M.op y y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by grind
  clear eq69705
  have eq105078 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))))))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2596 (M.op x (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))))) X1 X3
       have i₂ := eq2515 X0 x (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0)))))))))
       grind)
    | exact superpose eq2515 eq2596
    | exact resolve eq2596 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515 eq2596
  have eq225674 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X1) (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))))))) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5831 (M.op x (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))) X1
       have i₂ := eq7153 X0 x (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))
       grind)
    | exact superpose eq7153 eq5831
    | exact resolve eq5831 eq7153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5831 eq7153
  have eq6392687 : (σ y) ≠ (σ y) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq507 x y
       have i₂ := eq69706
       grind)
    | exact superpose eq69706 eq507
    | (have j0 := eq507 x y
       grind)
    | exact resolve eq507 eq69706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq69706
  have eq6392764 : (σ y) ≠ (σ y) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq6392687
  have eq6392765 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq6392764
  have eq6392850 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))))))) (σ (M.op y y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq105078 X0 (σ y) (σ x)
       have i₂ := eq6392765
       grind)
    | exact superpose eq6392765 eq105078
    | exact resolve eq105078 eq6392765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392765
  have eq6392856 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq6392850 x
       have i₂ := eq225674 x y
       grind)
    | exact superpose eq225674 eq6392850
    | exact resolve eq6392850 eq225674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392850
  have eq6392965 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6392856
       grind)
    | exact superpose eq6392856 eq16
    | exact resolve eq16 eq6392856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6392967 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq6392856
       grind)
    | exact superpose eq6392856 eq9
    | exact resolve eq9 eq6392856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392856
  have eq6400034 : ∀ X0 : G, y = (τ (σ x)) ∨ (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq6392967 X0
       grind)
    | exact superpose eq6392967 eq10
    | (have j1 := eq6392967 X0
       grind)
    | exact resolve eq10 eq6392967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392967
  have eq6400469 : ∀ X0 : G, x = y ∨ (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6400034 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6400034
    | (have j0 := eq6400034 X0
       grind)
    | exact resolve eq6400034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6400034
  have eq6402741 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq6400469 X0
       grind)
    | exact superpose eq6400469 eq16
    | (have j1 := eq6400469 X0
       grind)
    | exact resolve eq16 eq6400469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6400469
  have eq6402743 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq6402741 X0
       grind)
    | (have r₁ := eq6402741 X0
       have r₂ := eq44 x
       grind)
    | exact resolve eq6402741 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6402741
  have eq6403544 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq20 (σ x) x (σ y)
       have i₂ := eq6402743 x
       grind)
    | exact superpose eq6402743 eq20
    | exact resolve eq20 eq6402743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq6403546 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq133 (σ y) (σ x) x
       have i₂ := eq6402743 x
       grind)
    | exact superpose eq6402743 eq133
    | (have r₁ := eq133 (σ y) (σ x) x
       have r₂ := eq6402743 x
       grind)
    | exact resolve eq133 eq6402743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6402743
  have eq6403646 : (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq6403546
  have eq6403718 : (σ y) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq6403646
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6403646
    | exact resolve eq6403646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403646
  have eq6404451 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq6403718
       have i₂ := eq44 y
       grind)
    | exact superpose eq44 eq6403718
    | exact resolve eq6403718 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403718
  have eq6406827 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6403544
       grind)
    | exact superpose eq6403544 eq16
    | exact resolve eq16 eq6403544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403544
  have eq6446554 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))))))) (σ (M.op y y))) ∨ (σ y) = (σ (k x y)) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq105078 X0 (σ y) (σ x)
       have i₂ := eq6404451
       grind)
    | exact superpose eq6404451 eq105078
    | exact resolve eq105078 eq6404451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6404451
  have eq6446561 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq6446554 x
       have i₂ := eq225674 x y
       grind)
    | exact superpose eq225674 eq6446554
    | exact resolve eq6446554 eq225674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225674 eq6446554
  have eq6448580 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq1740 x y
       have i₂ := eq6446561
       grind)
    | exact superpose eq6446561 eq1740
    | (have j0 := eq1740 x y
       grind)
    | exact resolve eq1740 eq6446561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740 eq6446561
  have eq6448955 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq6448580
  have eq6449037 : y = (M.op x y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6448955
       have r₂ := eq6406827
       grind)
    | exact resolve eq6448955 eq6406827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6406827 eq6448955
  have eq6450695 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6392965
       have i₂ := eq6449037
       grind)
    | exact superpose eq6449037 eq6392965
    | exact resolve eq6392965 eq6449037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392965 eq6449037
  have eq6450746 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq6450695
  have eq6450747 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq6450746
  have eq6450768 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6450747
       grind)
    | exact superpose eq6450747 eq10
    | exact resolve eq10 eq6450747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6450747
  have eq6451218 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq6450768
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6450768
    | exact resolve eq6450768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6450768
  have eq6453142 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6451218
       grind)
    | exact superpose eq6451218 eq16
    | exact resolve eq16 eq6451218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6451218
  have eq6453144 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq6453142
       have r₂ := eq44 x
       grind)
    | exact resolve eq6453142 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453142
  have eq6454785 : ∀ X0 : G, y = (M.op (M.op y (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))))))))))) (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq105078 X0 y y
       have i₂ := eq6453144
       grind)
    | exact superpose eq6453144 eq105078
    | exact resolve eq105078 eq6453144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453144
  have eq6454787 : x = y := by
    first
    | (have i₁ := eq6454785 x
       have i₂ := eq105078 x y x
       grind)
    | (have i₁ := eq6454785 x
       have i₂ := eq105078 x x (M.op (M.op y (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (τ (M.op x x))))))))))))))))) (M.op y x))
       grind)
    | exact superpose eq105078 eq6454785
    | exact resolve eq6454785 eq105078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105078 eq6454785
  have eq6456361 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6454787
       grind)
    | exact superpose eq6454787 eq16
    | exact resolve eq16 eq6454787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6454787
  have eq6456363 : False := by grind
  exact eq6456363

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq40
    | exact resolve eq40 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq40
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq294 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq273
    | (have j0 := eq273 X0 X1
       grind)
    | exact resolve eq273 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq299 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       have j1 := eq89 X1 X0
       grind)
    | (have r₁ := eq294 X1 X0
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq294 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq294 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq294
  have eq344 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq299
    | exact resolve eq299 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq299 (σ X0) X1
       grind)
    | exact superpose eq299 eq15
    | (have j1 := eq299 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq381 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq344 X1 (τ X0)
       grind)
    | exact superpose eq344 eq18
    | (have j1 := eq344 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq344
  have eq1193 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq381 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq381
    | exact resolve eq381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq1231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1193 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1193
    | (have j0 := eq1193 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq2168 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq349 x y
       grind)
    | exact superpose eq349 eq16
    | (have j1 := eq349 x y
       grind)
    | exact resolve eq16 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq2257 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2168
       have i₂ := eq1231 x y
       grind)
    | exact superpose eq1231 eq2168
    | (have j1 := eq1231 (σ x) (σ y)
       grind)
    | (have r₁ := eq2168
       have r₂ := eq1231 x y
       grind)
    | (have r₁ := eq2168
       have r₂ := eq1231 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2168
       have r₂ := eq1231 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2168 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq2168
  have eq2258 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq2257
  have eq2261 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2258
       grind)
    | exact superpose eq2258 eq16
    | exact resolve eq16 eq2258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2258
  have eq2262 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq2261
       have r₂ := eq45 x
       grind)
    | exact resolve eq2261 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq2352 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2262
       grind)
    | exact superpose eq2262 eq16
    | exact resolve eq16 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2353 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2262
       grind)
    | exact superpose eq2262 eq10
    | exact resolve eq10 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq2397 : x = y := by
    first
    | (have i₁ := eq2353
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2353
    | exact resolve eq2353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2398 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2352
       have i₂ := eq45 x
       grind)
    | exact superpose eq45 eq2352
    | exact resolve eq2352 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq2352
  have eq2399 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2398
       have i₂ := eq2397
       grind)
    | exact superpose eq2397 eq2398
    | exact resolve eq2398 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397 eq2398
  have eq2400 : False := by grind
  exact eq2400

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_y_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
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
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq14 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq64 : y ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (k (M.op (M.op X0 X0) X1) (M.op X1 X2)) = (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X0) X1) (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X0) X1) (M.op X1 X2)
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X1) (M.op X1 X2)
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq76 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq126 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq134 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq134 eq16
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq259 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq305 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq405 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq236
    | exact resolve eq236 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq236 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq236
    | (have j0 := eq236 X0 y
       grind)
    | exact resolve eq236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq236
    | (have j0 := eq236 X0 (M.op x y)
       grind)
    | exact resolve eq236 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X0 X0) X1 X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X3
       have i₂ := eq54 X1 X0 X2
       grind)
    | exact superpose eq54 eq50
    | exact resolve eq50 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op (M.op X0 X0) X1) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x)) (M.op (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x))) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x))) (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x)))) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X0 X1) (M.op X1 X2) X3
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y) X0
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X0 X3 (M.op X0 X0)
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq54 X1 X1 (M.op X1 X2)
       have i₂ := eq50 X1 X1 X2
       grind)
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X3
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq14 X1 (M.op X1 X2) X2
       have i₂ := eq50 X1 X1 X2
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X0) X3 X4
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq14 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X0 X0) X1 X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq51 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0)
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq52 (M.op X2 X2)
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X4)) (M.op X0 X0)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 (M.op X0 X0) X3 X4
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq54 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq721 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq721
    | exact resolve eq721 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq818 : ∀ X0 X1 : G, (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq66 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq928 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (σ X0) (M.op (M.op (σ (k X0 X0)) X1) X2)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (σ X1) X1 X2
       have i₂ := eq94 X1 X1
       grind)
    | exact superpose eq94 eq51
    | (have j1 := eq94 X0 X0
       grind)
    | exact resolve eq51 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq936 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq12 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq942 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq936 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq947 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (σ X0) (M.op (M.op (σ (k X0 X0)) X1) X2)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq928 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq950 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq937 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq937 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq937 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq937 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq951 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq942 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq942 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq942 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq942 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq960 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq950
    | (have j0 := eq950 X0 X1
       grind)
    | exact resolve eq950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq961 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq951 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq951
    | (have j0 := eq951 X0 X1
       grind)
    | exact resolve eq951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq1121 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212 X0
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq212 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq212
    | exact resolve eq212 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1132 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 X0)
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq52
    | exact resolve eq52 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1245 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq216
    | exact resolve eq216 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq1251 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1245 eq14
    | exact resolve eq14 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1430 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq731 X0
       have i₂ := eq212 x
       grind)
    | exact superpose eq212 eq731
    | exact resolve eq731 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq1435 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1430 eq14
    | exact resolve eq14 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1506 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq732 X0
       have i₂ := eq212 sF2
       grind)
    | exact superpose eq212 eq732
    | exact resolve eq732 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq1517 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1506 eq1251
    | exact resolve eq1251 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq1506
  have eq3498 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq482 X0 X1 X2
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq482
    | exact resolve eq482 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq3623 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) := by
    first
    | exact superpose eq1435 eq3498
    | exact resolve eq3498 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3637 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X1 (M.op (M.op X0 x) (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq3498 eq50
    | exact resolve eq50 eq3498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3642 : ∀ X0 X1 : G, (M.op (M.op X1 x) (M.op x y)) = (M.op (M.op X1 (M.op (M.op X0 x) (M.op x y))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3637 X0 X1
       have i₂ := eq212 X1
       grind)
    | exact superpose eq212 eq3637
    | exact resolve eq3637 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq4224 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 X1 x (M.op X0 X1)
       have i₂ := eq50 (M.op X0 X1) (M.op X0 X1) (M.op X1 x)
       grind)
    | (have i₁ := eq745 X0 X0 X0 (M.op X0 X0)
       have i₂ := eq50 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq50 eq745
    | exact resolve eq745 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq4256 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4224 X0 X1
       have i₂ := eq212 (M.op X0 X1)
       grind)
    | exact superpose eq212 eq4224
    | exact resolve eq4224 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224
  have eq5291 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq591 X0 X1 X2
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq591
    | exact resolve eq591 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq5352 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op x x)) x) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq751 X0 (M.op x x) x
       have i₂ := eq5291 (M.op X0 (M.op x x)) x x
       grind)
    | exact superpose eq5291 eq751
    | exact resolve eq751 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5353 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) x) (M.op x y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op sF2 sF2) x)
       have i₂ := eq5291 (M.op (M.op sF2 sF2) x) sF2 x
       grind)
    | exact superpose eq5291 eq53
    | exact resolve eq53 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6198 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X3 X3)) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5291 (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X3 X3)) X3 x
       have i₂ := eq749 X0 X1 X2 (M.op X3 X3) x
       grind)
    | exact superpose eq749 eq5291
    | exact resolve eq5291 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6956 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) X4)) x) (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5291 (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X1 X1) X2) (M.op X2 X3)) X4)) X1 (M.op X1 X1)
       have i₂ := eq753 (M.op X1 X1) X2 X3 X0 X4
       grind)
    | exact superpose eq753 eq5291
    | exact resolve eq5291 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq6999 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X4)) x) (M.op x y)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq6956 X0 X1 x x X4
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq6956
    | exact resolve eq6956 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6956
  have eq9932 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq136
    | (have j0 := eq136 (M.op x y)
       grind)
    | exact resolve eq136 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq9969 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq9932
  have eq9974 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq135 eq9969
    | exact resolve eq9969 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq9969
  have eq10006 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq9974
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq9974 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9974
  have eq10042 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq10006 eq158
    | exact resolve eq158 eq10006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq10006
  have eq11081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11081
    | exact resolve eq11081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11081
  have eq11093 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq11082
       have r₂ := eq27
       grind)
    | exact resolve eq11082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11082
  have eq11095 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11093
    | exact resolve eq11093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11093
  have eq11101 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11095 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11095
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11095
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11095
       grind)
    | exact resolve eq12 eq11095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11095
  have eq11136 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq11101
  have eq11140 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11136
    | exact resolve eq11136 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11136
  have eq11141 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq11140
  have eq11157 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq11141 eq58
    | exact resolve eq58 eq11141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11141
  have eq11176 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq11157
    | exact resolve eq11157 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11157
  have eq11394 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq961 y x
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq961
    | (have j0 := eq961 y x
       grind)
    | exact resolve eq961 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11429 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11394
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11394
    | exact resolve eq11394 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11394
  have eq11538 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11429
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq11429
    | exact resolve eq11429 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11429
  have eq11628 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11538
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11538
    | exact resolve eq11538 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11538
  have eq11718 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11628
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11628
    | exact resolve eq11628 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11628
  have eq11802 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11718
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11718
    | exact resolve eq11718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11718
  have eq11874 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11802
    | exact resolve eq11802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11802
  have eq13062 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq11176
       grind)
    | exact superpose eq11176 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11176
  have eq13063 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13062
  have eq13066 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13063
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13063
    | exact resolve eq13063 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13063
  have eq13067 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13066
  have eq13090 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq13067
       grind)
    | exact superpose eq13067 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13067
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13067
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13067
       grind)
    | exact resolve eq12 eq13067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13091 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq13067
       grind)
    | exact superpose eq13067 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13067
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13067
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13067
       grind)
    | exact resolve eq13 eq13067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13067
  have eq13126 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13091
  have eq13127 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13090
  have eq13130 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13126
    | exact resolve eq13126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13126
  have eq13131 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13127
    | exact resolve eq13127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13127
  have eq13132 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13131
  have eq13774 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq13130
       grind)
    | exact superpose eq13130 eq73
    | exact resolve eq73 eq13130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13130
  have eq13792 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13774
    | exact resolve eq13774 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13774
  have eq13817 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq940 x y
       have i₂ := eq13132
       grind)
    | exact superpose eq13132 eq940
    | (have j0 := eq940 x y
       grind)
    | exact resolve eq940 eq13132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq13818 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq961 x y
       have i₂ := eq13132
       grind)
    | exact superpose eq13132 eq961
    | (have j0 := eq961 x y
       grind)
    | exact resolve eq961 eq13132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq13132
  have eq13821 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13818
  have eq13822 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13817
  have eq13824 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13821
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq13821
    | exact resolve eq13821 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13821
  have eq13825 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13822
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13822
    | exact resolve eq13822 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13822
  have eq13833 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13824
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13824
    | exact resolve eq13824 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13824
  have eq13834 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13825
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13825
    | exact resolve eq13825 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13825
  have eq13837 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13833
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13833
    | exact resolve eq13833 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13833
  have eq13838 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13834
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13834
    | exact resolve eq13834 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13834
  have eq13839 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13837
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13837
    | exact resolve eq13837 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13837
  have eq13840 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13838
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13838
    | exact resolve eq13838 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13838
  have eq13841 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13839
       have r₂ := eq77
       grind)
    | exact resolve eq13839 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq13839
  have eq13842 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13840
    | exact resolve eq13840 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13840
  have eq13843 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13842
  have eq13923 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13843 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13843
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13843
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq13843
       grind)
    | exact resolve eq13 eq13843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13843
  have eq13958 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13923
  have eq13963 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13958
    | exact resolve eq13958 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13958
  have eq14265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13963 eq13792
    | exact resolve eq13792 eq13963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13792 eq13963
  have eq14269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14265
  have eq14273 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14269
       have r₂ := eq27
       grind)
    | exact resolve eq14269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14269
  have eq14368 : ∀ X0 X1 X2 : G, (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (M.op (M.op (k X0 (σ (τ X0))) X1) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq947 (τ X0) X1 X2
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq947
    | (have j0 := eq947 (τ X0) X1 X2
       grind)
    | exact resolve eq947 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq947
  have eq14447 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X0 (M.op (M.op (k X0 X0) X1) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14368 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14368
    | (have j0 := eq14368 X0 X1 X2
       grind)
    | exact resolve eq14368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14368
  have eq14481 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X0 (M.op (M.op (k X0 X0) X1) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14447 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14447
    | (have j0 := eq14447 X0 X1 X2
       grind)
    | exact resolve eq14447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14447
  have eq14521 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14273 eq65
    | (have r₁ := eq65
       have r₂ := eq14273
       grind)
    | exact resolve eq65 eq14273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq14533 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14521
  have eq15194 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14533 eq58
    | exact resolve eq58 eq14533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15195 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14533 eq117
    | exact resolve eq117 eq14533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq15212 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq15195
  have eq15812 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13841 eq83
    | exact resolve eq83 eq13841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq15851 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq15812
    | exact resolve eq15812 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15812
  have eq15855 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15851 eq15194
    | exact resolve eq15194 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15194
  have eq15862 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15851 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15851
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15851
       grind)
    | exact resolve eq13 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15899 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq15862
  have eq15902 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq15855
  have eq15905 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15899
    | exact resolve eq15899 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15899
  have eq15908 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq15902
    | exact resolve eq15902 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15902
  have eq15948 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15212 eq15851
    | exact resolve eq15851 eq15212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15991 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq15948
  have eq16005 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq15991
       have r₂ := eq76
       grind)
    | exact resolve eq15991 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15991
  have eq16108 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15908
       grind)
    | exact superpose eq15908 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15908
  have eq16109 : x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq16108
  have eq16118 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16109
    | exact resolve eq16109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16109
  have eq16119 : x = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq16118
  have eq16162 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq16005
       grind)
    | exact superpose eq16005 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq16005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16005
  have eq16163 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq16162
  have eq16168 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16163
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16163
    | exact resolve eq16163 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16163
  have eq16204 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16168
       grind)
    | exact superpose eq16168 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16168
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16168
       grind)
    | exact resolve eq13 eq16168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16168
  have eq16241 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq16204
  have eq16245 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16241
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16241
    | exact resolve eq16241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16241
  have eq16251 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq16245
       grind)
    | exact superpose eq16245 eq73
    | exact resolve eq73 eq16245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16277 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq16251
    | exact resolve eq16251 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16251
  have eq16339 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16277 eq13841
    | exact resolve eq13841 eq16277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13841
  have eq16341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16277 eq15905
    | exact resolve eq15905 eq16277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15905
  have eq16346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq16341
  have eq16348 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq16339
  have eq16357 : x = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq16346
       have r₂ := eq27
       grind)
    | exact resolve eq16346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16346
  have eq16425 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16348 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16348
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16348
       grind)
    | exact resolve eq13 eq16348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16348
  have eq16462 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq16425
  have eq16470 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16462
    | exact resolve eq16462 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16462
  have eq16991 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16245
       have i₂ := eq16357
       grind)
    | exact superpose eq16357 eq16245
    | exact resolve eq16245 eq16357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16245 eq16357
  have eq17000 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16991
  have eq17030 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17000 eq28
    | exact resolve eq28 eq17000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17000
  have eq17227 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq17030
    | exact resolve eq17030 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17030
  have eq17228 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17227
  have eq17229 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17228 eq20
    | exact resolve eq20 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17231 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17228 eq52
    | exact resolve eq52 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17233 : y ≠ y ∨ (k x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17228 eq64
    | (have r₁ := eq64
       have r₂ := eq17228
       grind)
    | exact resolve eq64 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq17236 : y ≠ y ∨ x = (M.op y x) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17228 eq76
    | (have r₁ := eq76
       have r₂ := eq17228
       grind)
    | exact resolve eq76 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq17239 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17228 eq126
    | exact resolve eq126 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17283 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17228 eq422
    | exact resolve eq422 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq17299 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq17228
  have eq17300 : x = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq17236
  have eq17301 : (k x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq17233
  have eq17303 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17283 X0
       have i₂ := eq421 X0
       grind)
    | exact superpose eq421 eq17283
    | exact resolve eq17283 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq17283
  have eq17346 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17239 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq17239
    | exact resolve eq17239 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq17239
  have eq17353 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17229
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17229
    | exact resolve eq17229 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17229
  have eq17855 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17346 eq236
    | exact resolve eq236 eq17346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17948 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17855 x
       have i₂ := eq236 sF1 x
       grind)
    | exact superpose eq236 eq17855
    | exact resolve eq17855 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq17855
  have eq17956 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq17948
    | exact resolve eq17948 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17948
  have eq17959 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq17956
    | exact resolve eq17956 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17956
  have eq18026 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op (M.op (M.op X0 X0) x) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq212 (M.op (M.op X0 X0) x)
       grind)
    | exact superpose eq212 eq727
    | exact resolve eq727 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq18329 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) x) x) (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) x) x) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq18026 eq767
    | exact resolve eq767 eq18026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18026
  have eq18432 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) x) = X0 := by
    intro X0
    first
    | exact superpose eq3498 eq18329
    | exact resolve eq18329 eq3498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18329
  have eq18587 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op (M.op (M.op X0 X0) (σ x)) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 X1
       have i₂ := eq212 (M.op (M.op X0 X0) sF2)
       grind)
    | exact superpose eq212 eq728
    | exact resolve eq728 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq18712 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq18587 eq18587
    | exact resolve eq18587 eq18587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18771 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) x) (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) x) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq18587 eq767
    | exact resolve eq767 eq18587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18875 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq3498 eq18771
    | exact resolve eq18771 eq3498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18771
  have eq19110 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq730 X0 X1 X2 X3
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq730
    | exact resolve eq730 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq19111 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) x) (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19110 X0 X1 X2 X3
       have i₂ := eq212 (M.op X0 X1)
       grind)
    | exact superpose eq212 eq19110
    | exact resolve eq19110 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19110
  have eq19235 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 X2)) x) (M.op x y)) = (M.op (M.op (M.op X1 x) (M.op x y)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19111 X1 (M.op X0 X2) (M.op X2 x) (M.op (M.op X0 X0) x)
       have i₂ := eq747 X0 X2 x x
       grind)
    | exact superpose eq747 eq19111
    | exact resolve eq19111 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20730 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq726 X0 X1 X2 X3
       have i₂ := eq212 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq212 eq726
    | exact resolve eq726 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq20969 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op (M.op X1 X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq20730 eq20730
    | exact resolve eq20730 eq20730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20972 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (M.op (σ x) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq18587 eq20730
    | exact resolve eq20730 eq18587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18587
  have eq21039 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1) x) (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1) x) (M.op x y))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq767 X0 (M.op X1 X2) x
       have i₂ := eq20730 (M.op X0 (M.op X1 X2)) X1 X2 x
       grind)
    | exact superpose eq20730 eq767
    | exact resolve eq767 eq20730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21049 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) x) (M.op x y)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq745 X1 x x X0
       have i₂ := eq20730 (M.op X0 X0) X1 x (M.op x x)
       grind)
    | exact superpose eq20730 eq745
    | exact resolve eq745 eq20730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20730
  have eq21178 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 x) (M.op x y)) X1) x) (M.op x y)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21049 X0 X1
       have i₂ := eq212 X0
       grind)
    | exact superpose eq212 eq21049
    | exact resolve eq21049 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21049
  have eq21183 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq3498 eq21039
    | exact resolve eq21039 eq3498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21039
  have eq21963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16470 eq16277
    | exact resolve eq16277 eq16470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16277 eq16470
  have eq21971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq21963
  have eq21980 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21971
       have r₂ := eq27
       grind)
    | exact resolve eq21971 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21971
  have eq21987 : ∀ X0 : G, (σ (k x X0)) = (k (σ (M.op x y)) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21980 eq35
    | exact resolve eq35 eq21980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq21995 : (k x y) = (τ (k (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21980 eq58
    | exact resolve eq58 eq21980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq22085 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21980 eq15212
    | exact resolve eq15212 eq21980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15212 eq21980
  have eq22094 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq22085
  have eq22181 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151 eq21995
    | exact resolve eq21995 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21995
  have eq22186 : ∀ X0 : G, (σ (k x X0)) = (σ (k (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq21987
    | exact resolve eq21987 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq21987
  have eq23692 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22181 eq134
    | exact resolve eq134 eq22181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22181
  have eq23719 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23692
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq23692
    | exact resolve eq23692 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23692
  have eq25445 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23719 eq14533
    | exact resolve eq14533 eq23719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14533 eq23719
  have eq25455 : (M.op (σ y) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq25445
  have eq26010 : (τ (M.op (σ y) (σ x))) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25455 eq151
    | exact resolve eq151 eq25455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25455
  have eq27793 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) x) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq725 X0 X1 X2 X3
       have i₂ := eq212 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq212 eq725
    | exact resolve eq725 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq725
  have eq27905 : (τ (σ x)) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15851 eq26010
    | exact resolve eq26010 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851 eq26010
  have eq27948 : (τ (σ x)) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq27905
  have eq27961 : x = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq28 eq27948
    | exact resolve eq27948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27948
  have eq28160 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27793 X0 x x X1
       have i₂ := eq54 x X0 x
       grind)
    | exact superpose eq54 eq27793
    | exact resolve eq27793 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28165 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq27793 eq27793
    | exact resolve eq27793 eq27793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28241 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x) (M.op x y)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) x) (M.op x y))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq767 X0 X1 x
       have i₂ := eq27793 (M.op X0 X1) X1 X2 x
       grind)
    | exact superpose eq27793 eq767
    | exact resolve eq767 eq27793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28420 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq3498 eq28241
    | exact resolve eq28241 eq3498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28241
  have eq29835 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (k (σ X0) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17303 eq336
    | exact resolve eq336 eq17303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17303
  have eq29918 : ∀ X0 : G, (k X0 (τ (σ (M.op x y)))) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29835 X0
       have i₂ := eq336 X0 sF1
       grind)
    | exact superpose eq336 eq29835
    | exact resolve eq29835 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq29835
  have eq29943 : ∀ X0 : G, (k X0 y) = (k X0 (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq29918
    | exact resolve eq29918 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29918
  have eq29949 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq29943
    | exact resolve eq29943 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29943
  have eq33816 : ∀ X0 : G, (k (M.op x y) X0) = (τ (σ (k x X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22186 eq16
    | exact resolve eq16 eq22186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22186
  have eq33902 : ∀ X0 : G, (k x X0) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33816 X0
       have i₂ := eq16 (k x X0)
       grind)
    | exact superpose eq16 eq33816
    | exact resolve eq33816 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33816
  have eq34042 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ (M.op x y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33902 eq305
    | exact resolve eq305 eq33902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq33902
  have eq34151 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (k (σ (M.op x y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34042 X0
       have i₂ := eq259 X0
       grind)
    | exact superpose eq259 eq34042
    | exact resolve eq34042 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq34042
  have eq34927 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18432 eq17231
    | exact resolve eq17231 eq18432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35063 : (M.op x y) = (M.op (M.op (M.op (M.op x y) y) x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34927 eq52
    | exact resolve eq52 eq34927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35085 : (M.op x y) = (M.op (M.op (M.op (M.op x y) y) x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34927 eq17231
    | exact resolve eq17231 eq34927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17231
  have eq35159 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34927 eq3623
    | exact resolve eq3623 eq34927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623 eq34927
  have eq35223 : (M.op x y) = (M.op (M.op (M.op (M.op x y) y) x) y) ∨ x = (M.op x y) := by grind
  clear eq35085
  have eq50198 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) = (M.op (M.op (M.op x y) y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35223 eq767
    | exact resolve eq767 eq35223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35223
  have eq50224 : x = (M.op (M.op (M.op x y) y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1435 eq50198
    | exact resolve eq50198 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50198
  have eq50242 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50224 eq35063
    | exact resolve eq35063 eq50224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35063 eq50224
  have eq50311 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq50242
  have eq50360 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50311 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq50311
       grind)
    | exact resolve eq12 eq50311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50361 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50311 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq50311
       grind)
    | exact resolve eq13 eq50311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50311
  have eq50409 : (k x (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq50361
  have eq50410 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq50360
  have eq51239 : (k x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50409 eq29949
    | exact resolve eq29949 eq50409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50409
  have eq51249 : (k x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq51239
  have eq51547 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17301
       have i₂ := eq51249
       grind)
    | exact superpose eq51249 eq17301
    | exact resolve eq17301 eq51249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51249
  have eq51557 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq51547
  have eq51787 : (M.op x y) = (M.op (M.op (M.op y x) y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51557 eq35159
    | exact resolve eq35159 eq51557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35159 eq51557
  have eq51853 : (M.op x y) = (M.op (M.op (M.op y x) y) x) ∨ x = (M.op x y) := by grind
  clear eq51787
  have eq70130 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq16119
       grind)
    | exact superpose eq16119 eq44
    | exact resolve eq44 eq16119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16119
  have eq70190 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70130
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70130
    | exact resolve eq70130 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70130
  have eq70453 : (τ (σ x)) = (τ (k (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq70190 eq34151
    | exact resolve eq34151 eq70190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34151 eq70190
  have eq70466 : (τ (σ x)) = (τ (k (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq70453
  have eq70492 : (τ (σ x)) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq151 eq70466
    | exact resolve eq70466 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70466
  have eq70507 : x = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq70492
    | exact resolve eq70492 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq70492
  have eq70730 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq17300
       grind)
    | exact superpose eq17300 eq73
    | exact resolve eq73 eq17300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq17300
  have eq70779 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70730
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70730
    | exact resolve eq70730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70730
  have eq71379 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70779 eq17346
    | exact resolve eq17346 eq70779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17346 eq70779
  have eq71393 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq71379
  have eq71927 : (σ x) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17353 eq11874
    | exact resolve eq11874 eq17353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11874 eq17353
  have eq71958 : (σ x) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq71927
       have r₂ := eq27
       grind)
    | exact resolve eq71927 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71927
  have eq72576 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq71393 eq71958
    | (have r₁ := eq71958
       have r₂ := eq71393
       grind)
    | exact resolve eq71958 eq71393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71393 eq71958
  have eq72599 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq72576
  have eq72600 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq72599
  have eq83534 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq72600 eq62
    | exact resolve eq62 eq72600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq72600
  have eq83579 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq83534
    | exact resolve eq83534 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq83534
  have eq84858 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq83579 eq29949
    | exact resolve eq29949 eq83579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29949 eq83579
  have eq84872 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq84858
  have eq86158 : x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50410 eq17959
    | exact resolve eq17959 eq50410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17959 eq50410
  have eq86172 : x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq86158
  have eq89787 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq17301
       have i₂ := eq84872
       grind)
    | exact superpose eq84872 eq17301
    | exact resolve eq17301 eq84872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17301 eq84872
  have eq89806 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq89787
  have eq92940 : (M.op y y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1132 y
       have i₂ := eq89806
       grind)
    | exact superpose eq89806 eq1132
    | exact resolve eq1132 eq89806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq89806
  have eq93039 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq52 eq92940
    | exact resolve eq92940 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq92940
  have eq95152 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq767 y y x
       have i₂ := eq93039
       grind)
    | exact superpose eq93039 eq767
    | exact resolve eq767 eq93039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93039
  have eq95184 : x = y ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1435 eq95152
    | exact resolve eq95152 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq95152
  have eq95214 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq95184
       have r₂ := eq17299
       grind)
    | exact resolve eq95184 eq17299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17299 eq95184
  have eq95422 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51853
       have i₂ := eq95214
       grind)
    | exact superpose eq95214 eq51853
    | exact resolve eq51853 eq95214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51853
  have eq95445 : x ≠ x ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq95214
       grind)
    | exact superpose eq95214 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq95214
       grind)
    | exact resolve eq13 eq95214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95214
  have eq95497 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq95445
  have eq95501 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq95422
  have eq95533 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95497
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95497
    | exact resolve eq95497 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95497
  have eq95539 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95501
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95501
    | exact resolve eq95501 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95501
  have eq95571 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86172
       have i₂ := eq95533
       grind)
    | exact superpose eq95533 eq86172
    | exact resolve eq86172 eq95533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86172 eq95533
  have eq95581 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq95571
  have eq96083 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq95581 eq95539
    | exact resolve eq95539 eq95581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95539 eq95581
  have eq96156 : x = (M.op x y) := by grind
  clear eq96083
  have eq96215 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq96156 eq20
    | exact resolve eq20 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq96314 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op X0 x)) x) = X0 := by
    intro X0
    first
    | exact superpose eq96156 eq18432
    | exact resolve eq18432 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18432
  have eq96327 : x = (k y x) ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq96156 eq27961
    | exact resolve eq27961 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27961
  have eq96352 : x = (k x y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq96156 eq70507
    | exact resolve eq70507 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70507
  have eq96427 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96215
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96215
    | exact resolve eq96215 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96215
  have eq96470 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq96427 eq26
    | exact resolve eq26 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96595 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq96427 eq18875
    | exact resolve eq18875 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96910 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq96470 eq28165
    | exact resolve eq28165 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28165
  have eq96945 : ∀ X0 X1 : G, (M.op (M.op X1 x) x) = (M.op (M.op X1 (M.op (M.op X0 x) x)) X0) := by
    intro X0 X1
    first
    | exact superpose eq96156 eq3642
    | exact resolve eq3642 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3642
  have eq96994 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq20972 eq96945
    | exact resolve eq96945 eq20972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20972
  have eq97024 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq96945 x (M.op X0 X0)
       have i₂ := eq54 x X0 x
       grind)
    | exact superpose eq54 eq96945
    | exact resolve eq96945 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq96945
  have eq97334 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq96427 eq96994
    | exact resolve eq96994 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96994
  have eq97468 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) x) := by
    intro X0
    first
    | exact superpose eq1517 eq97024
    | exact resolve eq97024 eq1517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq97637 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ (M.op x y)) x) x) := by
    intro X0
    first
    | exact superpose eq96427 eq97468
    | exact resolve eq97468 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97468
  have eq98877 : (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq96910 eq18875
    | exact resolve eq18875 eq96910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18875 eq96910
  have eq99011 : (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq96427 eq98877
    | exact resolve eq98877 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98877
  have eq100737 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ (M.op x y)) x) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14273 eq97637
    | exact resolve eq97637 eq14273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97637
  have eq101052 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ (M.op x y)) x) x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq96156 eq100737
    | (have j0 := eq100737 X0
       grind)
    | exact resolve eq100737 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100737
  have eq103149 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op x x)) x) x) x) := by
    intro X0
    first
    | exact superpose eq96156 eq5352
    | exact resolve eq5352 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5352
  have eq103150 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op x y)) x) x) x) := by
    intro X0
    first
    | (have i₁ := eq103149 X0
       have i₂ := eq28160 X0 x
       grind)
    | exact superpose eq28160 eq103149
    | exact resolve eq103149 eq28160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28160 eq103149
  have eq103151 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 x) x) x) x) := by
    intro X0
    first
    | exact superpose eq96156 eq103150
    | exact resolve eq103150 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103150
  have eq103246 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq103151 (M.op X0 x)
       have i₂ := eq103151 X0
       grind)
    | exact superpose eq103151 eq103151
    | exact resolve eq103151 eq103151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104058 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X0 x) (M.op x y))) (σ (M.op x y))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96595 (M.op X0 (M.op (M.op sF4 sF4) x))
       have i₂ := eq5291 X0 sF4 x
       grind)
    | exact superpose eq5291 eq96595
    | exact resolve eq96595 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291
  have eq104106 : (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq96595 eq818
    | exact resolve eq818 eq96595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq96595
  have eq104255 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3498 eq104058
    | exact resolve eq104058 eq3498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3498 eq104058
  have eq108458 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X4)) x) x) := by
    intro X0 X1 X4
    first
    | exact superpose eq96156 eq6999
    | exact resolve eq6999 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6999
  have eq109080 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) x) (M.op x y))) = (M.op (M.op (M.op (M.op X2 X2) (M.op X0 X1)) x) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq4256 eq108458
    | exact resolve eq108458 eq4256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256
  have eq109715 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op (M.op X0 X1) x) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109080 X0 X1 X2
       have i₂ := eq108458 X2 X0 X1
       grind)
    | exact superpose eq108458 eq109080
    | exact resolve eq109080 eq108458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109080
  have eq109934 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op (M.op X0 X1) x) x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq96156 eq109715
    | exact resolve eq109715 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109715
  have eq112676 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op (σ x) (σ y)) X1) X2) (M.op X2 X3))) x) x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq97334 (M.op (M.op X3 X3) (M.op (M.op (M.op sF4 X1) X1) (M.op X1 X2))) X1
       have i₂ := eq745 (M.op sF4 X1) X1 X2 X3
       grind)
    | exact superpose eq745 eq97334
    | exact resolve eq97334 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq97334
  have eq112844 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112676 X0 X1 X2 x
       have i₂ := eq108458 X0 (M.op (M.op sF4 X1) X2) (M.op X2 x)
       grind)
    | exact superpose eq108458 eq112676
    | exact resolve eq112676 eq108458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112676
  have eq113471 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (M.op (σ y) X1) X2)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq14273 eq112844
    | exact resolve eq112844 eq14273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14273
  have eq114057 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (M.op (M.op (σ y) X1) X2)) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq96156 eq113471
    | (have j0 := eq113471 X0 X1 X2
       grind)
    | exact resolve eq113471 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113471
  have eq120694 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20969 X0 (M.op X1 X2) x x X3 X4
       have i₂ := eq109934 X1 X2 X0
       grind)
    | exact superpose eq109934 eq20969
    | exact resolve eq20969 eq109934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109934
  have eq124181 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 x) x) X1) x) x) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq96156 eq21178
    | exact resolve eq21178 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21178
  have eq125154 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op x X1)) x) (M.op (M.op (M.op (M.op X0 x) x) (M.op x X1)) x)) (M.op (M.op X0 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq750 (M.op (M.op (M.op (M.op X0 x) x) (M.op x X2)) x) x X2 X3 x
       have i₂ := eq124181 X0 (M.op x X2)
       grind)
    | exact superpose eq124181 eq750
    | exact resolve eq750 eq124181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq124181
  have eq125454 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op x X1)) (M.op (M.op (M.op X0 x) x) (M.op x X1))) x) (M.op (M.op X0 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq125154 X0 X1 X2 X3
       have i₂ := eq103246 (M.op (M.op (M.op X0 x) x) (M.op x X1))
       grind)
    | exact superpose eq103246 eq125154
    | exact resolve eq125154 eq103246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125154
  have eq125657 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 x) x) (M.op (M.op X0 X2) X3)) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq125454 X0 x X2 X3
       have i₂ := eq767 (M.op X0 x) x x
       grind)
    | exact superpose eq767 eq125454
    | exact resolve eq125454 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq125454
  have eq126951 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) x) x) (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) x) x)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21183 (M.op X1 x) X1 x
       have i₂ := eq103151 (M.op X1 x)
       grind)
    | exact superpose eq103151 eq21183
    | exact resolve eq21183 eq103151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103151
  have eq127204 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X2) (M.op X2 X3)) (M.op (M.op X0 (M.op X4 X5)) (M.op X0 (M.op X4 X5)))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq749 X1 X2 X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X0 (M.op X4 X5))) X4
       have i₂ := eq21183 X0 X4 X5
       grind)
    | exact superpose eq21183 eq749
    | exact resolve eq749 eq21183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq127285 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2))) (M.op (M.op (σ x) (σ y)) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18712 (M.op (M.op X0 (M.op (M.op sF4 X1) X2)) (M.op X0 (M.op (M.op sF4 X1) X2))) X1 X2
       have i₂ := eq21183 X0 (M.op sF4 X1) X2
       grind)
    | exact superpose eq21183 eq18712
    | exact resolve eq18712 eq21183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18712
  have eq127343 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) (M.op (M.op (σ x) (σ y)) X3)) = X0 := by
    intro X0 X3
    first
    | exact superpose eq112844 eq127285
    | exact resolve eq127285 eq112844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112844 eq127285
  have eq127398 : ∀ X0 X1 X4 X5 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 x) (M.op x y)) (M.op (M.op X0 (M.op X4 X5)) (M.op X0 (M.op X4 X5)))) X0) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq127204 X0 X1 x x X4 X5
       have i₂ := eq1121 X1 x x
       grind)
    | (have i₁ := eq127204 X0 X0 x y X4 X5
       have i₂ := eq1121 X0 X1 x
       grind)
    | exact superpose eq1121 eq127204
    | (have j0 := eq127204 X0 X1 x y X4 X5
       grind)
    | exact resolve eq127204 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127204
  have eq127520 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) x) (M.op (M.op (M.op (M.op X0 X1) x) x) x)) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq126951 X0 X1
       have i₂ := eq103246 (M.op (M.op (M.op (M.op X0 X1) x) x) x)
       grind)
    | exact superpose eq103246 eq126951
    | exact resolve eq126951 eq103246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103246 eq126951
  have eq127755 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X0) x) (M.op x y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq19111 eq127398
    | exact resolve eq127398 eq19111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19111 eq127398
  have eq127821 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) x) x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq127520 X0 X1
       have i₂ := eq96314 (M.op (M.op (M.op X0 X1) x) x)
       grind)
    | exact superpose eq96314 eq127520
    | exact resolve eq127520 eq96314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96314 eq127520
  have eq127952 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op X1 X0) x) x) X0) := by
    intro X0 X1
    first
    | exact superpose eq96156 eq127755
    | exact resolve eq127755 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127755
  have eq132311 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq28420 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28420
    | (have j0 := eq28420 x y X0
       grind)
    | exact resolve eq28420 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq132374 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq28420
    | (have j0 := eq28420 (σ x) (σ y) X0
       grind)
    | exact resolve eq28420 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28420
  have eq133161 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq96427 eq132374
    | exact resolve eq132374 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132374
  have eq133194 : ∀ X0 : G, x = (M.op (M.op x x) (M.op (M.op y y) X0)) := by
    intro X0
    first
    | exact superpose eq96156 eq132311
    | exact resolve eq132311 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132311
  have eq133984 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133161 x
       have i₂ := eq20969 (M.op sF4 sF4) sF3 sF3 x x x
       grind)
    | (have i₁ := eq133161 x
       have i₂ := eq20969 (M.op sF4 sF4) sF3 x x sF3 x
       grind)
    | exact superpose eq20969 eq133161
    | exact resolve eq133161 eq20969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133161
  have eq134289 : ∀ X0 X1 : G, x = (M.op (M.op x x) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133194 x
       have i₂ := eq20969 (M.op x x) y y x X0 X1
       grind)
    | (have i₁ := eq133194 x
       have i₂ := eq20969 (M.op x x) y X0 X1 y x
       grind)
    | exact superpose eq20969 eq133194
    | exact resolve eq133194 eq20969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20969
  have eq134330 : (M.op x x) = (M.op (M.op x x) (M.op y y)) := by
    first
    | (have i₁ := eq21183 (M.op x x) (M.op y y) x
       have i₂ := eq133194 x
       grind)
    | exact superpose eq133194 eq21183
    | exact resolve eq21183 eq133194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133194
  have eq134812 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq133984 eq21183
    | exact resolve eq21183 eq133984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133984
  have eq136800 : (M.op x x) = (M.op (M.op (M.op x x) (M.op x x)) y) := by
    first
    | (have i₁ := eq21183 (M.op x x) y y
       have i₂ := eq134330
       grind)
    | exact superpose eq134330 eq21183
    | exact resolve eq21183 eq134330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21183 eq134330
  have eq136935 : (M.op x x) = (M.op (M.op (M.op x x) (M.op x y)) y) := by
    first
    | (have i₁ := eq136800
       have i₂ := eq1121 x x x
       grind)
    | exact superpose eq1121 eq136800
    | exact resolve eq136800 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq136800
  have eq137004 : (M.op x x) = (M.op (M.op (M.op x x) x) y) := by
    first
    | exact superpose eq96156 eq136935
    | exact resolve eq136935 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136935
  have eq172621 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) x) x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq96156 eq5353
    | exact resolve eq5353 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353
  have eq172622 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq96427 eq172621
    | exact resolve eq172621 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172621
  have eq172700 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op X0 X1)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq172622 (M.op X1 x)
       have i₂ := eq108458 sF1 X1 x
       grind)
    | exact superpose eq108458 eq172622
    | exact resolve eq172622 eq108458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108458 eq172622
  have eq191593 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 x) x) X0) = (M.op (M.op (M.op X1 (M.op X0 X2)) x) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq96156 eq19235
    | exact resolve eq19235 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19235
  have eq197318 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq960 y x
       have i₂ := eq96327
       grind)
    | exact superpose eq96327 eq960
    | (have j0 := eq960 y x
       grind)
    | exact resolve eq960 eq96327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq96327
  have eq197324 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq197318
  have eq197338 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq197324
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq197324
    | exact resolve eq197324 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197324
  have eq197357 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq197338
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq197338
    | exact resolve eq197338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197338
  have eq197374 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq197357
    | exact resolve eq197357 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197357
  have eq197391 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq96427 eq197374
    | exact resolve eq197374 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197374
  have eq197402 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have r₁ := eq197391
       have r₂ := eq27
       grind)
    | exact resolve eq197391 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197391
  have eq197410 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq197402
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq197402
    | exact resolve eq197402 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197402
  have eq197417 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq197410
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq197410
    | exact resolve eq197410 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197410
  have eq197423 : x = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq197417
    | exact resolve eq197417 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq197417
  have eq197454 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq197423
       grind)
    | exact superpose eq197423 eq44
    | exact resolve eq44 eq197423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197516 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96427 eq197454
    | exact resolve eq197454 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197454
  have eq197534 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq197516
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq197516
    | exact resolve eq197516 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197516
  have eq197550 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96427 eq197534
    | exact resolve eq197534 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197534
  have eq197653 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq197550 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq197550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197550
  have eq197669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96470 eq197653
    | exact resolve eq197653 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197653
  have eq197684 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq197669
       have r₂ := eq27
       grind)
    | exact resolve eq197669 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197669
  have eq197695 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96470 eq197684
    | exact resolve eq197684 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197684
  have eq197696 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq197695
  have eq197754 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq197696 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq197696
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq197696
       grind)
    | exact resolve eq12 eq197696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197696
  have eq197834 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq197754
  have eq197886 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq96470 eq197834
    | exact resolve eq197834 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197834
  have eq197887 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq197886
  have eq198017 : (τ (σ y)) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq197887 eq151
    | exact resolve eq151 eq197887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq197887
  have eq198087 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq96156 eq198017
    | exact resolve eq198017 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198017
  have eq198096 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq198087
    | exact resolve eq198087 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198087
  have eq198347 : x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq197423
       have i₂ := eq198096
       grind)
    | exact superpose eq198096 eq197423
    | exact resolve eq197423 eq198096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197423 eq198096
  have eq198361 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq198347
  have eq198559 : (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq198361 eq99011
    | exact resolve eq99011 eq198361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99011
  have eq198564 : (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq198361 eq104106
    | exact resolve eq104106 eq198361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104106
  have eq198617 : (k (σ (M.op x y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq96470 eq198564
    | exact resolve eq198564 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198564
  have eq198618 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq96470 eq198559
    | exact resolve eq198559 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198559
  have eq198798 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (M.op (σ x) (σ y)) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq198618 eq127343
    | exact resolve eq127343 eq198618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127343 eq198618
  have eq198939 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq172700 eq198798
    | exact resolve eq198798 eq172700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172700 eq198798
  have eq206431 : (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq198361 eq198939
    | exact resolve eq198939 eq198361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198361 eq198939
  have eq206554 : (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) ∨ x = y := by grind
  clear eq206431
  have eq206652 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq96470 eq206554
    | exact resolve eq206554 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206554
  have eq206844 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ y) (σ y)) x) x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq206652 eq127952
    | exact resolve eq127952 eq206652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127952 eq206652
  have eq206858 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq206844
       have i₂ := eq127821 sF3 sF3
       grind)
    | exact superpose eq127821 eq206844
    | exact resolve eq206844 eq127821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127821 eq206844
  have eq228958 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96352
       grind)
    | exact superpose eq96352 eq44
    | exact resolve eq44 eq96352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq96352
  have eq229029 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq96427 eq228958
    | exact resolve eq228958 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228958
  have eq229047 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq229029
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq229029
    | exact resolve eq229029 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229029
  have eq229063 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq96427 eq229047
    | exact resolve eq229047 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229047
  have eq247677 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (k X0 X0) (M.op (M.op (M.op (k X0 X0) X1) X2) X3)) x) (M.op x y)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq751 X0 (M.op (M.op (k X0 X0) X1) X2) X3
       have i₂ := eq14481 X0 X1 X2
       grind)
    | exact superpose eq14481 eq751
    | (have j1 := eq14481 X0 X1 X2
       grind)
    | exact resolve eq751 eq14481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq14481
  have eq248173 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (k X0 X0) (M.op (M.op (M.op (k X0 X0) X1) X2) X3)) x) x) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq96156 eq247677
    | (have j0 := eq247677 X0 X1 X2 X3
       grind)
    | exact resolve eq247677 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247677
  have eq248326 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (k X0 X0) x) x) (M.op (M.op (k X0 X0) X1) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq248173 X0 X1 X2 x
       have i₂ := eq191593 (M.op (M.op (k X0 X0) X1) X2) (k X0 X0) x
       grind)
    | exact superpose eq191593 eq248173
    | (have j0 := eq248173 X0 X1 X2 x
       grind)
    | exact resolve eq248173 eq191593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248173
  have eq248405 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq248326 X0 x x
       have i₂ := eq125657 (k X0 X0) x x
       grind)
    | exact superpose eq125657 eq248326
    | (have j0 := eq248326 X0 x x
       grind)
    | exact resolve eq248326 eq125657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248326
  have eq248436 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq248405 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq248405 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq248405 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248405
  have eq248576 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq405 X0 X0
       have i₂ := eq248436 (τ X0)
       grind)
    | exact superpose eq248436 eq405
    | exact resolve eq405 eq248436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq248764 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq248576 X0
       have i₂ := eq248436 X0
       grind)
    | exact superpose eq248436 eq248576
    | exact resolve eq248576 eq248436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248576
  have eq249382 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) x) x) := by
    intro X0
    first
    | (have i₁ := eq97024 (τ X0)
       have i₂ := eq248764 X0
       grind)
    | exact superpose eq248764 eq97024
    | exact resolve eq97024 eq248764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248764
  have eq251186 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ y) (σ y))) x) x) ∨ x = y := by
    first
    | exact superpose eq206858 eq249382
    | exact resolve eq249382 eq206858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206858
  have eq251418 : (τ (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq251186
       have i₂ := eq249382 sF3
       grind)
    | exact superpose eq249382 eq251186
    | exact resolve eq251186 eq249382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249382 eq251186
  have eq251522 : y = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq29 eq251418
    | exact resolve eq251418 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq251418
  have eq251692 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq251522 eq126
    | exact resolve eq126 eq251522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq251522
  have eq251824 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq134 eq251692
    | exact resolve eq251692 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq251692
  have eq251852 : (k (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq251824 eq198617
    | exact resolve eq198617 eq251824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198617 eq251824
  have eq251869 : (k (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq251852
  have eq251970 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq251869 eq229063
    | exact resolve eq229063 eq251869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229063 eq251869
  have eq251986 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq251970
  have eq480308 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X3 X3)) x) x) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq96156 eq6198
    | exact resolve eq6198 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq480309 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) x) x) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq480308 X0 X1 X2 X3
       have i₂ := eq191593 X3 (M.op (M.op X0 X1) (M.op X1 X2)) X3
       grind)
    | exact superpose eq191593 eq480308
    | exact resolve eq480308 eq191593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480308
  have eq480310 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq480309 X0 X1 x X3
       have i₂ := eq191593 X1 (M.op X0 X1) x
       grind)
    | exact superpose eq191593 eq480309
    | exact resolve eq480309 eq191593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480309
  have eq481130 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (M.op (M.op (M.op (M.op (M.op (σ (M.op x y)) x) x) x) x) (M.op (σ y) X1)) X0) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq101052 eq480310
    | exact resolve eq480310 eq101052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101052
  have eq483717 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ y) X1)) X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq481130 X0 X1
       have i₂ := eq480310 sF1 x (M.op sF3 X1)
       grind)
    | exact superpose eq480310 eq481130
    | exact resolve eq481130 eq480310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480310 eq481130
  have eq485003 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ y) (σ y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq134812 eq483717
    | exact resolve eq483717 eq134812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134812 eq483717
  have eq491836 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) (M.op (M.op X0 X0) X1)) x) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq485003 eq27793
    | exact resolve eq27793 eq485003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27793 eq485003
  have eq492665 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (σ y) (σ y)) (M.op (M.op X0 X0) X1)) x) x) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq96156 eq491836
    | exact resolve eq491836 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491836
  have eq492965 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (σ y) (σ y)) x) x) (M.op X0 X0)) ∨ x = y := by
    intro X0 X2
    first
    | (have i₁ := eq492665 X0 X2 X2
       have i₂ := eq191593 (M.op X0 X0) (M.op sF3 sF3) X2
       grind)
    | exact superpose eq191593 eq492665
    | exact resolve eq492665 eq191593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191593 eq492665
  have eq493120 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) = (M.op (σ y) (M.op X0 X0)) ∨ x = y := by
    intro X0 X2
    first
    | (have i₁ := eq492965 X0 X2
       have i₂ := eq97024 sF3
       grind)
    | exact superpose eq97024 eq492965
    | exact resolve eq492965 eq97024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492965
  have eq530961 : ∀ X0 X1 : G, (M.op (σ y) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X1)) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq493120 eq114057
    | exact resolve eq114057 eq493120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114057 eq493120
  have eq531073 : ∀ X0 X1 : G, (M.op (σ y) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq530961 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530961
  have eq551620 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (M.op (M.op (M.op (σ y) X0) X1) X2)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X3)) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq531073 eq747
    | exact resolve eq747 eq531073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq531073
  have eq551867 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (M.op (M.op (M.op (σ y) X0) X1) X2)) (σ (M.op x y))) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq104255 eq551620
    | exact resolve eq551620 eq104255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104255 eq551620
  have eq551987 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq551867 x x x
       have i₂ := eq120694 (M.op sF3 sF1) sF3 x x x
       grind)
    | exact superpose eq120694 eq551867
    | exact resolve eq551867 eq120694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120694 eq551867
  have eq552069 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22094 eq551987
    | exact resolve eq551987 eq22094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22094 eq551987
  have eq552304 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq96470 eq552069
    | exact resolve eq552069 eq96470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552069
  have eq552358 : x = y ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq96156 eq552304
    | exact resolve eq552304 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552304
  have eq552359 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq552358
  have eq553832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq552359 eq251986
    | exact resolve eq251986 eq552359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251986 eq552359
  have eq554013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq553832
  have eq554096 : x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq554013
       have r₂ := eq27
       grind)
    | exact resolve eq554013 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554013
  have eq554222 : ∀ X0 X1 : G, y = (M.op (M.op x x) (M.op (M.op y X0) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq125657 y X0 X1
       have i₂ := eq554096
       grind)
    | exact superpose eq554096 eq125657
    | exact resolve eq125657 eq554096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125657 eq554096
  have eq554422 : x = y ∨ x = y := by
    first
    | (have i₁ := eq554222 x x
       have i₂ := eq134289 x x
       grind)
    | exact superpose eq134289 eq554222
    | exact resolve eq554222 eq134289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134289 eq554222
  have eq554423 : x = y := by grind
  clear eq554422
  have eq554569 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq554423
       grind)
    | exact superpose eq554423 eq24
    | exact resolve eq24 eq554423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq554777 : (M.op x x) = (M.op (M.op (M.op x x) x) x) := by
    first
    | (have i₁ := eq137004
       have i₂ := eq554423
       grind)
    | exact superpose eq554423 eq137004
    | exact resolve eq137004 eq554423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137004 eq554423
  have eq554876 : x = (M.op x x) := by
    first
    | (have i₁ := eq554777
       have i₂ := eq97024 x
       grind)
    | exact superpose eq97024 eq554777
    | exact resolve eq554777 eq97024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97024 eq554777
  have eq554974 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq554569
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq554569
    | exact resolve eq554569 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554569
  have eq555065 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq96427 eq554974
    | exact resolve eq554974 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554974
  have eq555459 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq555065 eq96470
    | exact resolve eq96470 eq555065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96470 eq555065
  have eq557059 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq555459 eq10042
    | exact resolve eq10042 eq555459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10042 eq555459
  have eq557467 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq557059
       have i₂ := eq248436 sF0
       grind)
    | exact superpose eq248436 eq557059
    | exact resolve eq557059 eq248436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248436 eq557059
  have eq557547 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq96156 eq557467
    | exact resolve eq557467 eq96156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96156 eq557467
  have eq557585 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq557547
       have i₂ := eq554876
       grind)
    | exact superpose eq554876 eq557547
    | exact resolve eq557547 eq554876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554876 eq557547
  have eq557666 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq557585 eq15
    | exact resolve eq15 eq557585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557585
  have eq557930 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq557666
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq557666
    | exact resolve eq557666 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq557666
  have eq558027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq96427 eq557930
    | exact resolve eq557930 eq96427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96427 eq557930
  have eq558071 : False := by grind
  exact eq558071

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq64 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq64 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq64 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq252 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq257 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq252 X0 X1
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq252 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq252 X1 X0
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq252 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq252
  have eq348 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq257 (σ X0) (σ X1)
       grind)
    | exact superpose eq257 eq15
    | exact resolve eq15 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq257 X0 X1
       grind)
    | exact superpose eq257 eq348
    | exact resolve eq348 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq348
  have eq354 : False := by grind
  exact eq354

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxx_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq43
    | exact resolve eq43 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq74 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq101 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq105 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq101
    | exact resolve eq101 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq105
    | exact resolve eq105 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq105
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq100
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq100 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq239 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq740 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq50
  have eq785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq117 eq79
    | (have j0 := eq79 (σ y) (σ x)
       grind)
    | exact resolve eq79 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq785
    | exact resolve eq785 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq789 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq786
       have r₂ := eq27
       grind)
    | exact resolve eq786 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq791 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq789
    | exact resolve eq789 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq795 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq791 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq791
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq791
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq791
       grind)
    | exact resolve eq12 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq795
       have r₂ := eq26
       grind)
    | exact resolve eq795 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq800 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq799
    | exact resolve eq799 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq931 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq800 eq117
    | exact resolve eq117 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq934 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq931
  have eq941 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq934 eq65
    | (have r₁ := eq65
       have r₂ := eq934
       grind)
    | exact resolve eq65 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq934
  have eq960 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq941
  have eq983 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq960 eq117
    | exact resolve eq117 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq960
  have eq986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq983
  have eq990 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq986
       have r₂ := eq27
       grind)
    | exact resolve eq986 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1182 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ y) x) (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq990 eq239
    | exact resolve eq239 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1398 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq243 X0
       have i₂ := eq239 X0
       grind)
    | exact superpose eq239 eq243
    | exact resolve eq243 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq1440 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) x) (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq791 eq1398
    | exact resolve eq1398 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq1398
  have eq1492 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1182 eq1440
    | exact resolve eq1440 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182 eq1440
  have eq1502 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1492
  have eq1515 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (M.op X0 X0) X1)) X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq1502 eq54
    | exact resolve eq54 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq1543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1515 x x
       have i₂ := eq54 x sF1 x
       grind)
    | exact superpose eq54 eq1515
    | exact resolve eq1515 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq1549 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1543
       have r₂ := eq27
       grind)
    | exact resolve eq1543 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1555 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) y) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq1549
       grind)
    | exact superpose eq1549 eq14
    | exact resolve eq14 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1613 : (M.op (M.op y y) (M.op y y)) = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq1555 (M.op (M.op y y) (M.op y y))
       have i₂ := eq54 y (M.op y y) (M.op y y)
       grind)
    | exact superpose eq54 eq1555
    | exact resolve eq1555 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1555
  have eq1625 : (M.op (M.op y x) (M.op x y)) = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq1613
       have i₂ := eq239 y
       grind)
    | exact superpose eq239 eq1613
    | exact resolve eq1613 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq1627 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq1625
       have i₂ := eq1549
       grind)
    | exact superpose eq1549 eq1625
    | exact resolve eq1625 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq1625
  have eq1638 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq1627 eq14
    | exact resolve eq14 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq1675 : ∀ X0 X1 : G, (M.op x y) = (M.op y (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1638 eq14
    | exact resolve eq14 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1694 : (M.op y y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) := by
    first
    | exact superpose eq1638 eq239
    | exact resolve eq239 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq52 eq1694
    | exact resolve eq1694 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1694
  have eq1716 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq1713
       grind)
    | exact superpose eq1713 eq107
    | exact resolve eq107 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1746 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq1716
    | exact resolve eq1716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1716
  have eq1747 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq740 X0
       have i₂ := eq239 x
       grind)
    | exact superpose eq239 eq740
    | exact resolve eq740 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq740
  have eq2029 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq1675 eq1747
    | exact resolve eq1747 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675 eq1747
  have eq2292 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2029 eq14
    | exact resolve eq14 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq2317 : x = y := by
    first
    | exact superpose eq1638 eq2292
    | exact resolve eq2292 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq2292
  have eq2380 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2317
       grind)
    | exact superpose eq2317 eq24
    | exact resolve eq24 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2385 : (σ (M.op x x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq2317
       grind)
    | exact superpose eq2317 eq107
    | exact resolve eq107 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2317
  have eq2412 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq1746 eq2385
    | exact resolve eq2385 eq1746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746 eq2385
  have eq2417 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2380
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2380
    | exact resolve eq2380 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2380
  have eq2418 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2412
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq2412
    | exact resolve eq2412 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq2412
  have eq2421 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2417 eq26
    | exact resolve eq26 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2417
  have eq2619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2418 eq2421
    | exact resolve eq2421 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418 eq2421
  have eq2620 : False := by grind
  exact eq2620
