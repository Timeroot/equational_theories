import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyx_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq71
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq71
    | exact resolve eq71 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq74
    | exact resolve eq74 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq268 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq270 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq36
  have eq280 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq268 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq268
    | exact resolve eq268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq280
  have eq406 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq408 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq406 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq406
    | (have j0 := eq406 X0
       grind)
    | exact resolve eq406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq478 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X2 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq55
    | exact resolve eq55 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq55 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq28 eq54
    | (have j0 := eq54 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq54 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 x (M.op X0 X0) X2
       have i₂ := eq55 x (M.op X0 X0) X0
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq595 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq281 X0
       grind)
    | exact superpose eq281 eq16
    | exact resolve eq16 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq815 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq479 (M.op X1 X1) x X0
       have i₂ := eq55 x (M.op X1 X1) X1
       grind)
    | exact superpose eq55 eq479
    | exact resolve eq479 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq479
  have eq863 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq815 (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq815
    | exact resolve eq815 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1349 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op X0 (M.op (M.op X3 X3) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq563 X3 (M.op X1 X0) (M.op (M.op X2 X2) X1)
       have i₂ := eq563 X2 X1 X0
       grind)
    | exact superpose eq563 eq563
    | exact resolve eq563 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1355 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq563 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq563
    | (have j0 := eq563 X0 x y
       grind)
    | exact resolve eq563 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2180 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op X0 X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq556 x (σ (M.op X0 X0))
       have i₂ := eq478 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq478 eq556
    | exact resolve eq556 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq556
  have eq10412 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq270 X0
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq270
    | (have j0 := eq270 X0
       grind)
    | exact resolve eq270 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq10413 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10412 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq10412
    | (have j0 := eq10412 X0
       grind)
    | exact resolve eq10412 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10412
  have eq10414 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10413 X0
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq10413
    | (have j0 := eq10413 X0
       grind)
    | exact resolve eq10413 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq10413
  have eq10776 : ∀ X0 : G, (k (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10414 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq10414
    | exact resolve eq10414 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10414
  have eq10838 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10776 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq10776
    | (have j0 := eq10776 X0
       grind)
    | exact resolve eq10776 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10776
  have eq10859 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10838 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq10838
    | (have j0 := eq10838 X0
       grind)
    | exact resolve eq10838 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10838
  have eq10874 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10859 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq10859
    | (have j0 := eq10859 X0
       grind)
    | exact resolve eq10859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10859
  have eq10877 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = X0 ∨ (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10874 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq10874
    | (have j0 := eq10874 X0
       grind)
    | exact resolve eq10874 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq10874
  have eq10880 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10877 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq10877
    | (have j0 := eq10877 X0
       grind)
    | exact resolve eq10877 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10877
  have eq25466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq25467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq25466
    | exact resolve eq25466 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25466
  have eq25472 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq25467
       have r₂ := eq29
       grind)
    | exact resolve eq25467 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25467
  have eq25478 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq25472 eq67
    | exact resolve eq67 eq25472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25472
  have eq25649 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq31 eq25478
    | exact resolve eq25478 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25478
  have eq25650 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25649
  have eq25658 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25650
       have i₂ := eq815 x X0
       grind)
    | (have i₁ := eq25650
       have i₂ := eq815 X0 x
       grind)
    | exact superpose eq815 eq25650
    | exact resolve eq25650 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq25674 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq408 x
       have i₂ := eq25650
       grind)
    | exact superpose eq25650 eq408
    | exact resolve eq408 eq25650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq25728 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq863 x X0
       have i₂ := eq25650
       grind)
    | exact superpose eq25650 eq863
    | exact resolve eq863 eq25650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq25753 : y = (M.op (M.op x y) (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1355 x
       have i₂ := eq25650
       grind)
    | exact superpose eq25650 eq1355
    | exact resolve eq1355 eq25650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq25778 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2180 x
       have i₂ := eq25650
       grind)
    | exact superpose eq25650 eq2180
    | exact resolve eq2180 eq25650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq25815 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25778
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq25778
    | exact resolve eq25778 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25778
  have eq25840 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25728 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq25728
    | (have j0 := eq25728 X0
       grind)
    | exact resolve eq25728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25728
  have eq25848 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25674
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25674
    | exact resolve eq25674 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25674
  have eq25859 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25848
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq25848
    | exact resolve eq25848 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25848
  have eq25862 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25859
       have i₂ := eq50
       grind)
    | exact superpose eq50 eq25859
    | exact resolve eq25859 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25859
  have eq25863 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25862
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq25862
    | exact resolve eq25862 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25862
  have eq25864 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25863
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25863
    | exact resolve eq25863 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25863
  have eq25865 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25864
  have eq124044 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op y x) (M.op (M.op X1 X1) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq25753 eq1349
    | exact resolve eq1349 eq25753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25753
  have eq124048 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq124044 X0 x
       have i₂ := eq563 x y x
       grind)
    | exact superpose eq563 eq124044
    | exact resolve eq124044 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124044
  have eq124097 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ x)) (M.op (M.op X1 X1) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq25815 eq1349
    | exact resolve eq1349 eq25815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349 eq25815
  have eq124102 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq124097 X0 X0
       have i₂ := eq563 X0 sF3 sF2
       grind)
    | exact superpose eq563 eq124097
    | exact resolve eq124097 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124097
  have eq154891 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124048 eq563
    | exact resolve eq563 eq124048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124048
  have eq157743 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124102 eq563
    | exact resolve eq563 eq124102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq124102
  have eq178985 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq154891 sF0
       have i₂ := eq25658 sF0
       grind)
    | exact superpose eq25658 eq154891
    | exact resolve eq154891 eq25658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25658 eq154891
  have eq179072 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq178985
  have eq184118 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq157743 sF4
       have i₂ := eq25840 sF4
       grind)
    | exact superpose eq25840 eq157743
    | exact resolve eq157743 eq25840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25840 eq157743
  have eq184195 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq184118
  have eq230902 : (σ (k x y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10880 x
       have i₂ := eq25650
       grind)
    | exact superpose eq25650 eq10880
    | exact resolve eq10880 eq25650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10880 eq25650
  have eq231002 : (σ (k x y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq230902
  have eq231057 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq231002
       have i₂ := eq50
       grind)
    | exact superpose eq50 eq231002
    | exact resolve eq231002 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq231002
  have eq2349116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq231057
       have i₂ := eq179072
       grind)
    | exact superpose eq179072 eq231057
    | exact resolve eq231057 eq179072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179072 eq231057
  have eq2349532 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2349116
  have eq2349542 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq2349532
    | exact resolve eq2349532 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349532
  have eq2349573 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2349542 eq25865
    | exact resolve eq25865 eq2349542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25865 eq2349542
  have eq2349600 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2349573
  have eq2349700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2349600 eq184195
    | exact resolve eq184195 eq2349600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184195 eq2349600
  have eq2349791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2349700
  have eq2349806 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2349791
       have r₂ := eq29
       grind)
    | exact resolve eq2349791 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349791
  have eq2349811 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2349806 eq31
    | exact resolve eq31 eq2349806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2349806
  have eq2351686 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq2349811
    | exact resolve eq2349811 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2349811
  have eq2351687 : x = y := by grind
  clear eq2351686
  have eq2351720 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq2351687
       grind)
    | exact superpose eq2351687 eq20
    | exact resolve eq20 eq2351687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2351721 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq2351687
       grind)
    | exact superpose eq2351687 eq26
    | exact resolve eq26 eq2351687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2351687
  have eq2352087 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2351721
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2351721
    | exact resolve eq2351721 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2351721
  have eq2352132 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2352087 eq28
    | exact resolve eq28 eq2352087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2352087
  have eq2355590 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2352132 eq67
    | exact resolve eq67 eq2352132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2352132
  have eq2357290 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2355590
       have i₂ := eq2351720
       grind)
    | exact superpose eq2351720 eq2355590
    | exact resolve eq2355590 eq2351720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351720 eq2355590
  have eq2357604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2357290 eq15
    | exact resolve eq15 eq2357290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357290
  have eq2358362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq2357604
    | exact resolve eq2357604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2357604
  have eq2358526 : False := by grind
  exact eq2358526

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq271 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq282 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq271
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq282
  have eq409 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq483 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq598 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq16
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq723 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (τ X0)
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq54
    | exact resolve eq54 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq981 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq483 X0 X1 x
       grind)
    | exact superpose eq483 eq14
    | exact resolve eq14 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq1568 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq565 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq409 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq409 eq565
    | exact resolve eq565 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq565
  have eq8030 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq981 X1 (τ X0) X2
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq981
    | exact resolve eq981 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq981
  have eq62427 : ∀ X0 : G, x = (M.op (M.op x x) (M.op y (σ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1568 y X0 x
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq1568
    | exact resolve eq1568 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq1568
  have eq62433 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq62427 x
       have i₂ := eq480 x x y
       grind)
    | exact superpose eq480 eq62427
    | exact resolve eq62427 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq62427
  have eq62434 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq62433
  have eq62454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62434 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq62434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62434
  have eq62455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq62454
    | exact resolve eq62454 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62454
  have eq62466 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq62455
       have r₂ := eq28
       grind)
    | exact resolve eq62455 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62455
  have eq62480 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq62466 eq8030
    | exact resolve eq8030 eq62466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8030 eq62466
  have eq62483 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62480 x
       have i₂ := eq723 x sF2 sF3
       grind)
    | exact superpose eq723 eq62480
    | exact resolve eq62480 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq62480
  have eq62484 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq62483
  have eq62495 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq62484 eq30
    | exact resolve eq30 eq62484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62484
  have eq62622 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq62495
    | exact resolve eq62495 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq62495
  have eq62623 : x = y := by grind
  clear eq62622
  have eq62999 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62623
       grind)
    | exact superpose eq62623 eq19
    | exact resolve eq19 eq62623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq63000 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62623
       grind)
    | exact superpose eq62623 eq25
    | exact resolve eq25 eq62623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62623
  have eq63128 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq63000
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63000
    | exact resolve eq63000 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq63000
  have eq63160 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63128 eq27
    | exact resolve eq27 eq63128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63128
  have eq64452 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63160 eq66
    | exact resolve eq66 eq63160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq63160
  have eq64775 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq64452
       have i₂ := eq62999
       grind)
    | exact superpose eq62999 eq64452
    | exact resolve eq64452 eq62999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62999 eq64452
  have eq64790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64775 eq15
    | exact resolve eq15 eq64775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64775
  have eq64871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64790
    | exact resolve eq64790 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64790
  have eq64894 : False := by grind
  exact eq64894

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq566 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq1369 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq566 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq566
    | (have j0 := eq566 X0 x y
       grind)
    | exact resolve eq566 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1370 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq566
    | (have j0 := eq566 X0 (σ x) (σ y)
       grind)
    | exact resolve eq566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq566 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq410 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq410 eq566
    | exact resolve eq566 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq1693 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1369 (M.op x (σ (M.op X0 X0)))
       have i₂ := eq410 X0 x (M.op x (σ (M.op X0 X0)))
       grind)
    | exact superpose eq410 eq1369
    | exact resolve eq1369 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1694 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1370 (M.op sF2 (σ (M.op X0 X0)))
       have i₂ := eq410 X0 sF2 (M.op sF2 (σ (M.op X0 X0)))
       grind)
    | exact superpose eq410 eq1370
    | exact resolve eq1370 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq1370
  have eq27832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq27833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq27832
    | exact resolve eq27832 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27832
  have eq27838 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq27833
       have r₂ := eq28
       grind)
    | exact resolve eq27833 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27833
  have eq27840 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq27838
    | exact resolve eq27838 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27838
  have eq27993 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27840 eq1685
    | exact resolve eq1685 eq27840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27840
  have eq27996 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1694 eq27993
    | exact resolve eq27993 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694 eq27993
  have eq27997 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27996
  have eq28161 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (σ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1685 x X0 x
       have i₂ := eq27997
       grind)
    | exact superpose eq27997 eq1685
    | exact resolve eq1685 eq27997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq27997
  have eq28164 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1693 eq28161
    | exact resolve eq28161 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693 eq28161
  have eq28165 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq28164
  have eq28222 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq28165 eq30
    | exact resolve eq30 eq28165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28165
  have eq28250 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq28222
    | exact resolve eq28222 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28222
  have eq28251 : x = y := by grind
  clear eq28250
  have eq28404 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq28251
       grind)
    | exact superpose eq28251 eq19
    | exact resolve eq19 eq28251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28405 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28251
       grind)
    | exact superpose eq28251 eq25
    | exact resolve eq25 eq28251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28251
  have eq28505 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28405
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28405
    | exact resolve eq28405 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28405
  have eq28520 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28505 eq27
    | exact resolve eq27 eq28505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28505
  have eq28809 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28520 eq66
    | exact resolve eq66 eq28520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq28520
  have eq28988 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq28809
       have i₂ := eq28404
       grind)
    | exact superpose eq28404 eq28809
    | exact resolve eq28809 eq28404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28404 eq28809
  have eq28991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28988 eq15
    | exact resolve eq15 eq28988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28988
  have eq29036 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq28991
    | exact resolve eq28991 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq28991
  have eq29045 : False := by grind
  exact eq29045

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq15
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq37
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (τ X0)
       have i₂ := eq22 (τ X0)
       grind)
    | exact superpose eq22 eq28
    | exact resolve eq28 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq50 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq50
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq118 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq114
    | (have j0 := eq114 X0 X1
       grind)
    | exact resolve eq114 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq148 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (σ X0) X1 X2
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq61
    | exact resolve eq61 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq61 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq184 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq10
    | exact resolve eq10 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1637 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 X0 X2 X3 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq60 X1 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1692 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1637 X0 X1 x x
       have i₂ := eq60 X0 x x X0
       grind)
    | exact superpose eq60 eq1637
    | (have j0 := eq1637 X0 X1 x x
       grind)
    | exact resolve eq1637 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1637
  have eq1693 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq4086 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq16
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq6000 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq163 X0 X1 x
       grind)
    | exact superpose eq163 eq9
    | exact resolve eq9 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq13873 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6000 X1 (τ X0) X2
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq6000
    | exact resolve eq6000 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6000
  have eq54561 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 X1)) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq148 X1 X2 (τ X0)
       have i₂ := eq184 X0
       grind)
    | exact superpose eq184 eq148
    | exact resolve eq148 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq184
  have eq59181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4086
       have i₂ := eq1693 x y
       grind)
    | exact superpose eq1693 eq4086
    | (have j1 := eq1693 (M.op (σ x) (σ y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq4086
       have r₂ := eq1693 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4086
       have r₂ := eq1693 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4086 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693 eq4086
  have eq59185 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59181
  have eq806209 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13873 X0 (σ x) (σ y)
       have i₂ := eq59185
       grind)
    | exact superpose eq59185 eq13873
    | exact resolve eq13873 eq59185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13873 eq59185
  have eq806228 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq806209 x
       have i₂ := eq54561 x x (σ x)
       grind)
    | exact superpose eq54561 eq806209
    | exact resolve eq806209 eq54561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54561 eq806209
  have eq806229 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq806228
  have eq806260 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq806229
       grind)
    | exact superpose eq806229 eq10
    | exact resolve eq10 eq806229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806229
  have eq806327 : x = y ∨ x = y := by
    first
    | (have i₁ := eq806260
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq806260
    | exact resolve eq806260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806260
  have eq806328 : x = y := by grind
  clear eq806327
  have eq807097 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq806328
       grind)
    | exact superpose eq806328 eq16
    | exact resolve eq16 eq806328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806328
  have eq807098 : False := by grind
  exact eq807098

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq16 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq179 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (k X0 X0)) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X2) (k X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (k X1 X1) (k X0 X0)
       have i₂ := eq179 X1 (k X0 X0) X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X2 X3 : G, (M.op X0 (k X2 X2)) = (M.op X0 (k X3 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq543 x X2 (M.op X0 (k X3 X3))
       have i₂ := eq179 x X0 X3
       grind)
    | exact superpose eq179 eq543
    | exact resolve eq543 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op (k X1 X1) X0)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq181 x (M.op (k X1 X1) X0) X3
       have i₂ := eq543 X1 x X0
       grind)
    | exact superpose eq543 eq181
    | exact resolve eq181 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq569 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X0) = (M.op (k X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X1 (M.op (k X2 X2) X0) x
       have i₂ := eq543 X2 x X0
       grind)
    | exact superpose eq543 eq179
    | exact resolve eq179 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 X2 X3 : G, (k X2 X2) = (M.op (M.op (k X0 X0) (k X1 X1)) (k X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq543 X0 X3 (k X2 X2)
       have i₂ := eq562 (k X0 X0) X2 X1
       grind)
    | (have i₁ := eq543 X0 X3 (k X2 X2)
       have i₂ := eq562 (k X0 X0) X1 X2
       grind)
    | exact superpose eq562 eq543
    | exact resolve eq543 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq607 : ∀ X1 X2 : G, (k X2 X2) = (k X1 X1) := by
    intro X1 X2
    first
    | (have i₁ := eq606 x X1 X2 x
       have i₂ := eq543 x x (k X1 X1)
       grind)
    | exact superpose eq543 eq606
    | exact resolve eq606 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq668 : ∀ X0 X1 : G, (k X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq607 X0 (σ X1)
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq607 (σ X1) X0
       grind)
    | exact superpose eq607 eq10
    | exact resolve eq10 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (k x x) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97
       have i₂ := eq607 x sF2
       grind)
    | (have i₁ := eq97
       have i₂ := eq607 sF2 x
       grind)
    | exact superpose eq607 eq97
    | exact resolve eq97 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq728 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq668 X1 x
       have i₂ := eq668 x X0
       grind)
    | exact superpose eq668 eq668
    | exact resolve eq668 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq728 x X1
       have i₂ := eq728 X0 x
       grind)
    | exact superpose eq728 eq728
    | exact resolve eq728 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq668 X1 x
       have i₂ := eq728 X0 x
       grind)
    | exact superpose eq728 eq668
    | exact resolve eq668 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1579 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op (k X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq568
    | exact resolve eq568 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (k X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq568 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq568
    | (have j0 := eq568 x X0 y
       grind)
    | exact resolve eq568 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1589 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (k X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq568
    | (have j0 := eq568 (σ x) X0 (σ y)
       grind)
    | exact resolve eq568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1643 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1644 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1646 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1644
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1644
    | exact resolve eq1644 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1647 : (M.op x y) = (k y x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1643
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1643
    | exact resolve eq1643 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1698 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (σ (k X0 X0)) x)) := by
    intro X0
    first
    | (have i₁ := eq1588 x
       have i₂ := eq668 x X0
       grind)
    | exact superpose eq668 eq1588
    | exact resolve eq1588 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq1588
  have eq1919 : ∀ X0 X1 X2 : G, (M.op (k X2 X2) (M.op (k X1 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq569 (M.op (k X1 X1) X0) X0 X2
       have i₂ := eq1579 X0 X1
       grind)
    | exact superpose eq1579 eq569
    | exact resolve eq569 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq1920 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq568 (M.op (k X1 X1) X0) X0 X2
       have i₂ := eq1579 X0 X1
       grind)
    | exact superpose eq1579 eq568
    | exact resolve eq568 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1921 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X0) = (M.op X0 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq543 X0 X2 (M.op (k X1 X1) X0)
       have i₂ := eq1579 X0 X1
       grind)
    | exact superpose eq1579 eq543
    | exact resolve eq543 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq1579
  have eq1993 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X3) (M.op X0 (k X2 X2))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1920 (M.op X0 (k X2 X2)) x X3
       have i₂ := eq179 x X0 X2
       grind)
    | exact superpose eq179 eq1920
    | exact resolve eq1920 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1920
  have eq3655 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1647
       grind)
    | exact superpose eq1647 eq39
    | exact resolve eq39 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq3656 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq3655
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3655
    | exact resolve eq3655 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3655
  have eq3658 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq3656
    | exact resolve eq3656 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3656
  have eq8079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq3658 eq1646
    | exact resolve eq1646 eq3658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646 eq3658
  have eq8086 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq8079
       have r₂ := eq27
       grind)
    | exact resolve eq8079 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8079
  have eq8134 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq8086 eq677
    | exact resolve eq677 eq8086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq8086
  have eq8228 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq8134
    | exact resolve eq8134 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8134
  have eq8229 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8228
  have eq8316 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq607 x X0
       have i₂ := eq8229
       grind)
    | exact superpose eq8229 eq607
    | exact resolve eq607 eq8229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq8327 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1068 x X0
       have i₂ := eq8229
       grind)
    | exact superpose eq8229 eq1068
    | exact resolve eq1068 eq8229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq8328 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1093 x X0
       have i₂ := eq8229
       grind)
    | exact superpose eq8229 eq1093
    | exact resolve eq1093 eq8229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq8362 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1589 x
       have i₂ := eq8229
       grind)
    | exact superpose eq8229 eq1589
    | exact resolve eq1589 eq8229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq8364 : y = (M.op (M.op x y) (M.op (σ y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1698 x
       have i₂ := eq8229
       grind)
    | exact superpose eq8229 eq1698
    | exact resolve eq1698 eq8229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq8368 : ∀ X0 X1 : G, (M.op y (M.op (k X0 X0) X1)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1919 X1 X0 x
       have i₂ := eq8229
       grind)
    | exact superpose eq8229 eq1919
    | exact resolve eq1919 eq8229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8371 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op X1 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1921 X1 X0 x
       have i₂ := eq8229
       grind)
    | exact superpose eq8229 eq1921
    | exact resolve eq1921 eq8229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921 eq8229
  have eq8400 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq8371 eq8368
    | exact resolve eq8368 eq8371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8368 eq8371
  have eq8404 : y = (M.op (M.op x y) (M.op (σ y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8364
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8364
    | exact resolve eq8364 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8364
  have eq8423 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8328 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8328
    | (have j0 := eq8328 X0
       grind)
    | exact resolve eq8328 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8328
  have eq8424 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8327 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8327
    | (have j0 := eq8327 X0
       grind)
    | exact resolve eq8327 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8327
  have eq8485 : y = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8316 eq8423
    | exact resolve eq8423 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8423
  have eq8486 : y = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8316 eq8424
    | exact resolve eq8424 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8424
  have eq8523 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8485 eq8486
    | exact resolve eq8486 eq8485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8485 eq8486
  have eq8528 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8523
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8523
    | exact resolve eq8523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8523
  have eq8531 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq8528 eq31
    | exact resolve eq31 eq8528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8552 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq8531
    | exact resolve eq8531 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8531
  have eq8553 : y = (σ y) ∨ x = y := by grind
  clear eq8552
  have eq8558 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq8553
       grind)
    | exact superpose eq8553 eq40
    | exact resolve eq40 eq8553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq8568 : x ≠ (σ y) ∨ x = y := by grind
  clear eq8553
  have eq8815 : ∀ X1 X2 : G, (M.op y (M.op (k X1 X1) X2)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq1919 X2 X1 x
       have i₂ := eq8316 x
       grind)
    | exact superpose eq8316 eq1919
    | exact resolve eq1919 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq8898 : ∀ X2 : G, (M.op y (M.op y X2)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2
    first
    | exact superpose eq8316 eq8815
    | exact resolve eq8815 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8815
  have eq9010 : ∀ X2 : G, (M.op (σ y) (M.op (σ y) X2)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2
    first
    | exact superpose eq8528 eq8898
    | exact resolve eq8898 eq8528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8898
  have eq10425 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op y y) ∨ y = (σ x) := by
    first
    | (have i₁ := eq8362
       have i₂ := eq11 sF2 y
       grind)
    | exact superpose eq11 eq8362
    | (have j1 := eq11 (σ x) y
       grind)
    | exact resolve eq8362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8362
  have eq10436 : (σ x) = (k y y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (σ x) := by
    first
    | (have i₁ := eq10425
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq10425
    | exact resolve eq10425 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10425
  have eq10442 : y = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (σ x) := by
    first
    | exact superpose eq8316 eq10436
    | exact resolve eq10436 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10436
  have eq10443 : y = (σ x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10442
  have eq10449 : (σ x) = (σ y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8528 eq10443
    | exact resolve eq10443 eq8528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10443
  have eq10450 : (σ x) = (σ y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) y)) ∨ x = y := by grind
  clear eq10449
  have eq10455 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8528 eq10450
    | exact resolve eq10450 eq8528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10450
  have eq10953 : ∀ X0 : G, (M.op (σ y) x) = (M.op y (M.op (M.op x y) (k X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8404 eq1993
    | exact resolve eq1993 eq8404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993 eq8404
  have eq10958 : (M.op (σ y) x) = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8316 eq10953
    | exact resolve eq10953 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10953
  have eq10964 : (M.op x y) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8400 eq10958
    | exact resolve eq10958 eq8400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8400 eq10958
  have eq10982 : (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ x = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10964 eq11
    | (have j0 := eq11 x (σ y)
       grind)
    | exact resolve eq11 eq10964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10964
  have eq10986 : (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10982
       have r₂ := eq8568
       grind)
    | exact resolve eq10982 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8568 eq10982
  have eq10992 : x = (k (σ y) (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10986
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq10986
    | exact resolve eq10986 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10986
  have eq10997 : x = y ∨ (M.op x y) = (k x (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8316 eq10992
    | exact resolve eq10992 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10992
  have eq10998 : (M.op x y) = (k x (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10997
  have eq11033 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10998 eq8558
    | exact resolve eq8558 eq10998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8558 eq10998
  have eq11035 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11033
  have eq11037 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11035
    | exact resolve eq11035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11035
  have eq11039 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq11037
    | exact resolve eq11037 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11037
  have eq12370 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (σ y) (M.op (k X0 X0) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10455 eq568
    | exact resolve eq568 eq10455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq10455
  have eq12372 : (k (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8316 eq12370
    | exact resolve eq12370 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8316 eq12370
  have eq12377 : (k (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8528 eq12372
    | exact resolve eq12372 eq8528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8528 eq12372
  have eq12382 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9010 eq12377
    | exact resolve eq12377 eq9010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9010 eq12377
  have eq12387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11039 eq12382
    | exact resolve eq12382 eq11039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11039 eq12382
  have eq12392 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12387
       have r₂ := eq27
       grind)
    | exact resolve eq12387 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12387
  have eq12398 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12392 eq31
    | exact resolve eq31 eq12392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12392
  have eq12427 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12398
    | exact resolve eq12398 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12398
  have eq12428 : x = y := by grind
  clear eq12427
  have eq12440 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12428
       grind)
    | exact superpose eq12428 eq18
    | exact resolve eq18 eq12428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12441 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq12428
       grind)
    | exact superpose eq12428 eq24
    | exact resolve eq24 eq12428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12428
  have eq12454 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12441
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12441
    | exact resolve eq12441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12441
  have eq12455 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq12440
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq12440
    | exact resolve eq12440 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12440
  have eq12456 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12454 eq26
    | exact resolve eq26 eq12454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12454
  have eq12481 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12456
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq12456
    | exact resolve eq12456 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq12456
  have eq12489 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq12455
       grind)
    | exact superpose eq12455 eq39
    | exact resolve eq39 eq12455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq12455
  have eq12678 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12489
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12489
    | exact resolve eq12489 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12489
  have eq12732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12481 eq12678
    | exact resolve eq12678 eq12481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12481 eq12678
  have eq12752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12732
    | exact resolve eq12732 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12732
  have eq12756 : False := by grind
  exact eq12756

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyx_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq71
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq71
    | exact resolve eq71 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq22 eq74
    | exact resolve eq74 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq87 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq91 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq87
  have eq92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq91
  have eq123 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
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
  have eq268 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq36
  have eq279 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq268 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq268
    | exact resolve eq268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq280 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq279
  have eq323 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq40
  have eq406 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq408 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq406 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq406
    | (have j0 := eq406 X0
       grind)
    | exact resolve eq406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq483 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X2 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq55
    | exact resolve eq55 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq55 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq28 eq54
    | (have j0 := eq54 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq54 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 x (M.op X0 X0) X2
       have i₂ := eq55 x (M.op X0 X0) X0
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq600 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq16
    | exact resolve eq16 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq815 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq484 (M.op X1 X1) x X0
       have i₂ := eq55 x (M.op X1 X1) X1
       grind)
    | exact superpose eq55 eq484
    | exact resolve eq484 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq484
  have eq863 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq815 (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq815
    | exact resolve eq815 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq1355 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq567 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq567
    | (have j0 := eq567 X0 x y
       grind)
    | exact resolve eq567 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq2180 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op X0 X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq560 x (σ (M.op X0 X0))
       have i₂ := eq483 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq483 eq560
    | exact resolve eq560 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq560
  have eq10407 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq600 X0
       grind)
    | exact superpose eq600 eq323
    | (have j0 := eq323 X0
       grind)
    | exact resolve eq323 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq10408 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10407 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq10407
    | (have j0 := eq10407 X0
       grind)
    | exact resolve eq10407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10407
  have eq10409 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10408 X0
       have i₂ := eq600 X0
       grind)
    | exact superpose eq600 eq10408
    | (have j0 := eq10408 X0
       grind)
    | exact resolve eq10408 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600 eq10408
  have eq10776 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10409 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq10409
    | exact resolve eq10409 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq10409
  have eq10834 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ X0)) (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10776 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq10776
    | (have j0 := eq10776 X0
       grind)
    | exact resolve eq10776 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10776
  have eq10854 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10834 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq10834
    | (have j0 := eq10834 X0
       grind)
    | exact resolve eq10834 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10834
  have eq10869 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10854 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq10854
    | (have j0 := eq10854 X0
       grind)
    | exact resolve eq10854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10854
  have eq10872 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10869 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq10869
    | (have j0 := eq10869 X0
       grind)
    | exact resolve eq10869 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10869
  have eq10875 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10872 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq10872
    | (have j0 := eq10872 X0
       grind)
    | exact resolve eq10872 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10872
  have eq25396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq25397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq28 eq25396
    | exact resolve eq25396 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25396
  have eq25402 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq25397
       have r₂ := eq29
       grind)
    | exact resolve eq25397 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25397
  have eq25406 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq25402 eq123
    | exact resolve eq123 eq25402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq25402
  have eq25576 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq25406
    | exact resolve eq25406 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25406
  have eq25577 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25576
  have eq25598 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq408 y
       have i₂ := eq25577
       grind)
    | exact superpose eq25577 eq408
    | exact resolve eq408 eq25577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq25652 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq863 y X0
       have i₂ := eq25577
       grind)
    | exact superpose eq25577 eq863
    | exact resolve eq863 eq25577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq25677 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1355 y
       have i₂ := eq25577
       grind)
    | exact superpose eq25577 eq1355
    | exact resolve eq1355 eq25577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq25702 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2180 y
       have i₂ := eq25577
       grind)
    | exact superpose eq25577 eq2180
    | exact resolve eq2180 eq25577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq25739 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25702
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25702
    | exact resolve eq25702 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25702
  have eq25763 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25652 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25652
    | (have j0 := eq25652 X0
       grind)
    | exact resolve eq25652 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25652
  have eq25771 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25598
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25598
    | exact resolve eq25598 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25598
  have eq25781 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25771
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq25771
    | exact resolve eq25771 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25771
  have eq25784 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25781
       have i₂ := eq50
       grind)
    | exact superpose eq50 eq25781
    | exact resolve eq25781 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25781
  have eq25785 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25784
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq25784
    | exact resolve eq25784 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25784
  have eq25786 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25785
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25785
    | exact resolve eq25785 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25785
  have eq25787 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25786
  have eq124236 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25677 eq486
    | exact resolve eq486 eq25677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25677
  have eq124423 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25739 eq486
    | exact resolve eq486 eq25739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq25739
  have eq168680 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq124236 y
       have i₂ := eq25577
       grind)
    | exact superpose eq25577 eq124236
    | exact resolve eq124236 eq25577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124236
  have eq168750 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq168680
  have eq176095 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq124423 x
       have i₂ := eq25763 x
       grind)
    | exact superpose eq25763 eq124423
    | exact resolve eq124423 eq25763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25763 eq124423
  have eq176295 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq176095
  have eq230906 : (σ (k x y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10875 y
       have i₂ := eq25577
       grind)
    | exact superpose eq25577 eq10875
    | exact resolve eq10875 eq25577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875 eq25577
  have eq231000 : (σ (k x y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq230906
  have eq231054 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq231000
       have i₂ := eq50
       grind)
    | exact superpose eq50 eq231000
    | exact resolve eq231000 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq231000
  have eq2059660 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq231054
       have i₂ := eq168750
       grind)
    | exact superpose eq168750 eq231054
    | exact resolve eq231054 eq168750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168750 eq231054
  have eq2060090 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2059660
  have eq2060098 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq2060090
    | exact resolve eq2060090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060090
  have eq2060129 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2060098 eq25787
    | exact resolve eq25787 eq2060098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25787 eq2060098
  have eq2060156 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2060129
  have eq2060184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2060156 eq176295
    | exact resolve eq176295 eq2060156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176295 eq2060156
  have eq2060262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2060184
  have eq2060273 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2060262
       have r₂ := eq29
       grind)
    | exact resolve eq2060262 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060262
  have eq2060277 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2060273 eq31
    | exact resolve eq31 eq2060273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2060273
  have eq2060711 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq2060277
    | exact resolve eq2060277 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2060277
  have eq2060712 : x = y := by grind
  clear eq2060711
  have eq2060745 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq2060712
       grind)
    | exact superpose eq2060712 eq20
    | exact resolve eq20 eq2060712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2060746 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq2060712
       grind)
    | exact superpose eq2060712 eq26
    | exact resolve eq26 eq2060712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2060712
  have eq2061114 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2060746
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2060746
    | exact resolve eq2060746 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2060746
  have eq2061157 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2061114 eq28
    | exact resolve eq28 eq2061114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2061114
  have eq2063862 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2061157 eq67
    | exact resolve eq67 eq2061157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2061157
  have eq2065498 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2063862
       have i₂ := eq2060745
       grind)
    | exact superpose eq2060745 eq2063862
    | exact resolve eq2063862 eq2060745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060745 eq2063862
  have eq2065807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2065498 eq15
    | exact resolve eq15 eq2065498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065498
  have eq2066579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq2065807
    | exact resolve eq2065807 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2065807
  have eq2066753 : False := by grind
  exact eq2066753

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_pyx_pyx_pxy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq76 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq85
  have eq133 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X1) X1
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq141 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq145 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq141 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq141 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq155 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq76 X1 (σ X0)
       grind)
    | (have r₁ := eq145 X0 X0
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq145 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq145
  have eq162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq155
    | (have j0 := eq155 X0 X1
       grind)
    | exact resolve eq155 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq163 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq167 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq163
    | exact resolve eq163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq163 x y
       grind)
    | exact superpose eq163 eq16
    | exact resolve eq16 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq223 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq167 X0 (τ X1)
       grind)
    | exact superpose eq167 eq17
    | exact resolve eq17 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq167
  have eq237 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq223
    | exact resolve eq223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq243 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq237
    | exact resolve eq237 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq263 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq178
       have i₂ := eq243 x y
       grind)
    | exact superpose eq243 eq178
    | exact resolve eq178 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq243
  have eq264 : False := by grind
  exact eq264

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_x_pxy_x_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq164 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq169 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq169
    | (have j0 := eq169 X0 X1
       grind)
    | exact resolve eq169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq368 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq174 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq174 x y
       grind)
    | exact superpose eq174 eq16
    | (have j1 := eq174 x y
       grind)
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq401 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq403 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq368
  have eq725 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq403
    | exact resolve eq403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq807 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq725 (τ X1) X0
       grind)
    | exact superpose eq725 eq18
    | (have j1 := eq725 (τ X1) X0
       grind)
    | exact resolve eq18 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq725
  have eq949 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq401 X0 X1
       grind)
    | exact superpose eq401 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq401 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq401 X0 X1
       grind)
    | exact resolve eq13 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 : G, (σ X0) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq401 X0 X1
       grind)
    | exact superpose eq401 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq401 X1 X0
       grind)
    | exact resolve eq12 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq956 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq959 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq956 X0 X1
       have j1 := eq951 X0 X1
       grind)
    | (have r₁ := eq956 X0 X1
       have r₂ := eq951 X0 X1
       grind)
    | exact resolve eq956 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq956
  have eq1096 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq959 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq959
    | exact resolve eq959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1237 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1096 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1355 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq807 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq807
    | exact resolve eq807 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq1415 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1355 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1355
    | (have j0 := eq1355 X0 X1
       grind)
    | exact resolve eq1355 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1619 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq379
       have i₂ := eq1096 x y
       grind)
    | exact superpose eq1096 eq379
    | (have j1 := eq1096 x y
       grind)
    | exact resolve eq379 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq1096
  have eq1626 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1619
  have eq1632 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq392 x y
       have i₂ := eq1626
       grind)
    | exact superpose eq1626 eq392
    | (have j0 := eq392 x y
       grind)
    | exact resolve eq392 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq1626
  have eq1641 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1632
  have eq1642 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1641
  have eq1651 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1642
       grind)
    | exact superpose eq1642 eq16
    | exact resolve eq16 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1656 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1237 (σ x) (σ y)
       have i₂ := eq1642
       grind)
    | exact superpose eq1642 eq1237
    | (have j0 := eq1237 (σ x) (σ y)
       grind)
    | (have r₁ := eq1237 (σ x) (σ y)
       have r₂ := eq1642
       grind)
    | exact resolve eq1237 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq1642
  have eq1659 : (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1656
  have eq1662 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq1659
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1659
    | exact resolve eq1659 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq1743 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1415 y x
       have i₂ := eq1662
       grind)
    | exact superpose eq1662 eq1415
    | (have j0 := eq1415 y x
       grind)
    | exact resolve eq1415 eq1662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq1662
  have eq1809 : x = (M.op x y) := by
    first
    | (have r₁ := eq1743
       have r₂ := eq1651
       grind)
    | exact resolve eq1743 eq1651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1907 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1651
       have i₂ := eq1809
       grind)
    | exact superpose eq1809 eq1651
    | exact resolve eq1651 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651 eq1809
  have eq1912 : False := by grind
  exact eq1912
