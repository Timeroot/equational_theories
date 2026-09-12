import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X2 (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op x X0) X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k X1 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X2
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq71 X1 X1
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq71
    | exact resolve eq71 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 X0 (M.op X0 X1)
       have i₂ := eq71 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq63 X0 X1 (M.op X1 X0)
       have i₂ := eq71 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq71 eq63
    | exact resolve eq63 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) (M.op X0 X2)) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq78 (M.op X0 X2) X0 X3
       have i₂ := eq78 X0 X2 X1
       grind)
    | (have i₁ := eq78 (M.op X0 X2) X0 X3
       have i₂ := eq78 X0 X1 X2
       grind)
    | exact superpose eq78 eq78
    | exact resolve eq78 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq308 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq307 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq307
    | (have j0 := eq307 (σ X0) (σ X1)
       grind)
    | exact resolve eq307 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq307 (σ X1) X0
       grind)
    | exact superpose eq307 eq28
    | (have j1 := eq307 (σ X1) X0
       grind)
    | exact resolve eq28 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq328 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq307 (τ X1) X0
       grind)
    | exact superpose eq307 eq17
    | (have j1 := eq307 (τ X1) X0
       grind)
    | exact resolve eq17 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (M.op X0 X0) X1 (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq308 y x
       grind)
    | exact superpose eq308 eq16
    | (have j1 := eq308 y x
       grind)
    | exact resolve eq16 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) X1) (M.op X2 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq308 X0 X0
       grind)
    | exact superpose eq308 eq9
    | (have j1 := eq308 X0 X0
       grind)
    | exact resolve eq9 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op (σ X0) (σ X0)) X2) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq308 X0 X1
       grind)
    | exact superpose eq308 eq9
    | (have j1 := eq308 X0 X1
       grind)
    | exact resolve eq9 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (M.op (M.op (σ X1) (σ X1)) (σ X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (σ X1) (σ X0)
       have i₂ := eq308 X0 X1
       grind)
    | exact superpose eq308 eq71
    | (have j1 := eq308 X0 X1
       grind)
    | exact resolve eq71 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (M.op (σ X1) X2) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 (σ X1) (σ X0) X2
       have i₂ := eq308 X0 X1
       grind)
    | exact superpose eq308 eq78
    | (have j1 := eq308 X0 X1
       grind)
    | exact resolve eq78 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq408 (M.op X0 X1) (M.op (M.op X0 X0) X0)
       have i₂ := eq61 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq61 eq408
    | exact resolve eq408 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq592 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq566 X0 X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq566
    | exact resolve eq566 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq676 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq592 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)
       have i₂ := eq592 X0 X1
       grind)
    | exact superpose eq592 eq592
    | exact resolve eq592 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X0 X0) X0) X2
       have i₂ := eq592 X0 X1
       grind)
    | exact superpose eq592 eq9
    | exact resolve eq9 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq9 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq676
    | exact resolve eq676 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq731 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq691 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0) X2
       have i₂ := eq592 X0 X1
       grind)
    | exact superpose eq592 eq691
    | exact resolve eq691 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq767 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (k X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq67 X1 X1
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq67
    | exact resolve eq67 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq876 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 X0 X2
       have i₂ := eq712 X0 X1
       grind)
    | (have i₁ := eq63 X1 X1 X2
       have i₂ := eq712 X1 X1
       grind)
    | exact superpose eq712 eq63
    | exact resolve eq63 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq881 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X0) (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq712 X0 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X1)
       have i₂ := eq712 X1 X1
       grind)
    | exact superpose eq712 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (M.op X0 X1) X2
       have i₂ := eq712 X0 X1
       grind)
    | (have i₁ := eq71 (M.op X1 X1) X1
       have i₂ := eq712 X1 X1
       grind)
    | exact superpose eq712 eq71
    | exact resolve eq71 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq876 X0 X1 (M.op (M.op X0 X0) (M.op X0 X1))
       have i₂ := eq712 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have i₁ := eq876 X0 X0 (M.op (M.op X0 X0) X1)
       have i₂ := eq712 (M.op X0 X0) X1
       grind)
    | exact superpose eq712 eq876
    | exact resolve eq876 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq1057 : ∀ X0 X1 : G, (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) = (k X0 (σ (M.op (τ X0) X1))) ∨ (M.op (τ X0) X1) = (M.op (τ X0) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 (M.op (τ X0) X1) X0
       have i₂ := eq71 (τ X0) X1
       grind)
    | (have i₁ := eq328 (M.op (τ X1) (τ X1)) X1
       have i₂ := eq71 (τ X1) X1
       grind)
    | exact superpose eq71 eq328
    | (have j0 := eq328 (M.op (τ X0) X1) X0
       grind)
    | exact resolve eq328 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq1284 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq492
       have i₂ := eq307 y x
       grind)
    | exact superpose eq307 eq492
    | (have j1 := eq307 (σ y) (σ x)
       grind)
    | exact resolve eq492 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1287 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1284
  have eq1288 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq1287
       have i₂ := eq308 x y
       grind)
    | exact superpose eq308 eq1287
    | (have j1 := eq308 x y
       grind)
    | exact resolve eq1287 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq1290 : (k x (τ (σ y))) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq325 (σ y) x
       have i₂ := eq1287
       grind)
    | exact superpose eq1287 eq325
    | (have j0 := eq325 (σ y) x
       grind)
    | exact resolve eq325 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq1298 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq81 (σ y) (σ x) X0
       have i₂ := eq1287
       grind)
    | exact superpose eq1287 eq81
    | exact resolve eq81 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312 : x = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1290
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1290
    | exact resolve eq1290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1313 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1312
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1312
    | exact resolve eq1312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1954 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (k (τ X0) (τ X0))) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq497 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq497
    | exact resolve eq497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq2026 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 (σ (τ X0))) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1954 X0 X1 X2
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1954
    | (have j0 := eq1954 X0 X1 X2
       grind)
    | exact resolve eq1954 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1954
  have eq2031 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2026 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2026
    | (have j0 := eq2026 X0 X1 X2
       grind)
    | exact resolve eq2026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2026
  have eq2085 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op X0 (M.op (k X0 X0) X1)) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82 (k X0 X0) X1 (M.op x X0)
       have i₂ := eq2031 X0 X1 x
       grind)
    | exact superpose eq2031 eq82
    | (have j1 := eq2031 X0 X1 x
       grind)
    | exact resolve eq82 eq2031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2031
  have eq2227 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (M.op (σ (τ X0)) (σ (τ X0))) X2) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq498 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq498
    | (have j0 := eq498 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq498 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq2272 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (M.op (σ (τ X0)) (σ (τ X0))) X2) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2227 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2227
    | (have j0 := eq2227 X0 X1 X2
       grind)
    | exact resolve eq2227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2275 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (k X0 X1)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2272 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2272
    | (have j0 := eq2272 X0 X1 X2
       grind)
    | exact resolve eq2272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2276 : ∀ X0 X1 X2 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op (M.op (M.op X0 X0) X2) (k X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2275 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2275
    | (have j0 := eq2275 X0 X1 X2
       grind)
    | exact resolve eq2275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2277 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (k X0 X1)) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2276 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2276
    | (have j0 := eq2276 X0 X1 X2
       grind)
    | exact resolve eq2276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276
  have eq2327 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (M.op (M.op (k X0 X1) X2) (k X0 X1)) X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 (k X0 X1) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq2277 X0 X1 x
       grind)
    | exact superpose eq2277 eq81
    | (have j1 := eq2277 X0 X1 X2
       grind)
    | exact resolve eq81 eq2277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2277
  have eq3616 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1298 (σ x)
       have i₂ := eq1313
       grind)
    | exact superpose eq1313 eq1298
    | exact resolve eq1298 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298 eq1313
  have eq3646 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq3616
  have eq4471 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ x = (M.op y x) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq3646
       grind)
    | exact superpose eq3646 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq3646
       grind)
    | exact resolve eq12 eq3646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq4506 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ x = (M.op y x) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq4471 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4471
  have eq6938 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ x = (M.op y x) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq4506 (σ X0)
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq4506
    | exact resolve eq4506 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4506
  have eq13747 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1288
       grind)
    | exact superpose eq1288 eq16
    | exact resolve eq16 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq13842 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (M.op X0 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2085 X0 (M.op X0 X1)
       have i₂ := eq691 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq691 eq2085
    | (have j0 := eq2085 X0 X1
       grind)
    | exact resolve eq2085 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085
  have eq18826 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1287
       have i₂ := eq6938 x
       grind)
    | exact superpose eq6938 eq1287
    | exact resolve eq1287 eq6938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq6938
  have eq18928 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq18826
  have eq19174 : (k x y) = (τ (σ x)) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq18928
       grind)
    | exact superpose eq18928 eq10
    | exact resolve eq10 eq18928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18928
  have eq19233 : x = (k x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq19174
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19174
    | exact resolve eq19174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19174
  have eq19234 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq19233
  have eq19236 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq307 x y
       have i₂ := eq19234
       grind)
    | exact superpose eq19234 eq307
    | (have j0 := eq307 y x
       grind)
    | exact resolve eq307 eq19234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19267 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq19236
  have eq19269 : (σ y) ≠ (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13747
       have i₂ := eq19267
       grind)
    | exact superpose eq19267 eq13747
    | exact resolve eq13747 eq19267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13747
  have eq19272 : y ≠ y ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19267
       grind)
    | exact superpose eq19267 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19267
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19267
       grind)
    | exact resolve eq13 eq19267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19276 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq78 x y X0
       have i₂ := eq19267
       grind)
    | exact superpose eq19267 eq78
    | exact resolve eq78 eq19267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19267
  have eq19313 : (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq19272
  have eq19316 : (σ y) ≠ (σ y) ∨ x = (M.op y x) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq19269
  have eq19317 : (σ x) = (σ (k x y)) ∨ x = (M.op y x) := by grind
  clear eq19316
  have eq23580 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19317
       have i₂ := eq19313
       grind)
    | exact superpose eq19313 eq19317
    | exact resolve eq19317 eq19313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19313 eq19317
  have eq23636 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq23580
  have eq26714 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq502 X1 X0
       have i₂ := eq307 X1 X0
       grind)
    | exact superpose eq307 eq502
    | (have j0 := eq502 X1 X0
       have j1 := eq307 (σ X1) (σ X0)
       grind)
    | exact resolve eq502 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq502
  have eq53433 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2327 X0 X0 (M.op X0 X1)
       have i₂ := eq13842 X0 X1
       grind)
    | exact superpose eq13842 eq2327
    | (have j0 := eq2327 X0 X0 x
       have j1 := eq13842 X0 X1
       grind)
    | exact resolve eq2327 eq13842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327 eq13842
  have eq53515 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53433
  have eq54834 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) = (k (σ X0) (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1057 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1057
    | exact resolve eq1057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq55133 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k X0 (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54834 X0 X1
       have i₂ := eq15 X0 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq54834
    | (have j0 := eq54834 X0 X1
       grind)
    | exact resolve eq54834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54834
  have eq190414 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1000 X0 X1
       have i₂ := eq712 X0 X1
       grind)
    | (have i₁ := eq1000 X1 X1
       have i₂ := eq712 X1 X1
       grind)
    | exact superpose eq712 eq1000
    | exact resolve eq1000 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq1000
  have eq253832 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X0)) = (σ (k X0 (M.op X0 X2))) ∨ (M.op X0 X2) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55133 X0 X2
       have i₂ := eq71 X0 X1
       grind)
    | (have i₁ := eq55133 X1 X1
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq55133
    | (have j0 := eq55133 X0 X2
       grind)
    | exact resolve eq55133 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq55133
  have eq370766 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X0) (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))) (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53515 (M.op (M.op X0 X1) X0) (M.op x X0)
       have i₂ := eq81 X0 X1 x
       grind)
    | exact superpose eq81 eq53515
    | (have j0 := eq53515 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact resolve eq53515 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53515
  have eq371927 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq370766 X0 X1
       have i₂ := eq9 X0 (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq370766
    | (have j0 := eq370766 X0 X1
       grind)
    | exact resolve eq370766 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370766
  have eq372146 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X0 ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq371927 X0 X1
       have i₂ := eq81 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq81 eq371927
    | (have j0 := eq371927 X0 X1
       grind)
    | exact resolve eq371927 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371927
  have eq372738 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq372146 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))))
       have i₂ := eq190414 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq190414 eq372146
    | exact resolve eq372146 eq190414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190414 eq372146
  have eq373090 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq372738 X0
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq372738
    | (have j0 := eq372738 X0
       grind)
    | exact resolve eq372738 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372738
  have eq373163 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq373090 X0
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq373090
    | (have j0 := eq373090 X0
       grind)
    | exact resolve eq373090 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq373090
  have eq373231 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq373163 X0
       have j1 := eq881 X0 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq373163 x
       have r₂ := eq881 x x x
       grind)
    | exact resolve eq373163 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq373163
  have eq374949 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq373231 (M.op (M.op X0 X0) X0)
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq373231
    | exact resolve eq373231 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373231
  have eq375746 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq374949 (σ X0)
       grind)
    | exact superpose eq374949 eq15
    | exact resolve eq15 eq374949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375826 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq374949 (τ X0)
       grind)
    | exact superpose eq374949 eq31
    | exact resolve eq31 eq374949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq376121 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq375826 X0
       have i₂ := eq374949 X0
       grind)
    | exact superpose eq374949 eq375826
    | exact resolve eq375826 eq374949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375826
  have eq376198 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq375746 X0
       have i₂ := eq374949 X0
       grind)
    | exact superpose eq374949 eq375746
    | exact resolve eq375746 eq374949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374949 eq375746
  have eq376962 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq376121 X0
       grind)
    | exact superpose eq376121 eq9
    | exact resolve eq9 eq376121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376121
  have eq377733 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq376198 X0
       grind)
    | exact superpose eq376198 eq9
    | exact resolve eq9 eq376198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376198
  have eq379981 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X2) (τ X0)) = (τ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376962 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq81 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq81 eq376962
    | exact resolve eq376962 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376962
  have eq382630 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq377733 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq377733
    | exact resolve eq377733 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382631 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq377733 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq81 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq81 eq377733
    | exact resolve eq377733 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq389022 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (τ (M.op (M.op (σ X0) X2) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq379981 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq379981
    | exact resolve eq379981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379981
  have eq426670 : ∀ X0 X1 : G, (τ (M.op (M.op (σ x) X1) (σ x))) = (M.op (M.op (M.op x x) X0) (M.op x x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq389022 (M.op x x) X1 x
       have i₂ := eq23636
       grind)
    | exact superpose eq23636 eq389022
    | exact resolve eq389022 eq23636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23636 eq389022
  have eq428078 : ∀ X1 : G, x = (τ (M.op (M.op (σ x) X1) (σ x))) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X1
    first
    | (have i₁ := eq426670 x X1
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq426670
    | exact resolve eq426670 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426670
  have eq428638 : x = (τ (σ (M.op (M.op x x) x))) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq428078 x
       have i₂ := eq382630 x x
       grind)
    | exact superpose eq382630 eq428078
    | exact resolve eq428078 eq382630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428078
  have eq428883 : x = (M.op (M.op x x) x) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq428638
       have i₂ := eq10 (M.op (M.op x x) x)
       grind)
    | exact superpose eq10 eq428638
    | exact resolve eq428638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428638
  have eq847470 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19276 x
       have i₂ := eq428883
       grind)
    | exact superpose eq428883 eq19276
    | exact resolve eq19276 eq428883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19276 eq428883
  have eq847914 : y = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq847470
  have eq848198 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq847914
       grind)
    | exact superpose eq847914 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq847914
       grind)
    | exact resolve eq12 eq847914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847914
  have eq848531 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq848198 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848198
  have eq851971 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19234
       have i₂ := eq848531 x
       grind)
    | exact superpose eq848531 eq19234
    | exact resolve eq19234 eq848531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19234 eq848531
  have eq852243 : x = (M.op y x) := by grind
  clear eq851971
  have eq852545 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq78 y x X0
       have i₂ := eq852243
       grind)
    | exact superpose eq852243 eq78
    | exact resolve eq78 eq852243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq852563 : ∀ X0 : G, x = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq691 y x x
       have i₂ := eq852243
       grind)
    | exact superpose eq852243 eq691
    | exact resolve eq691 eq852243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq852566 : ∀ X0 : G, y = (M.op (M.op x x) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq731 y x x
       have i₂ := eq852243
       grind)
    | exact superpose eq852243 eq731
    | exact resolve eq731 eq852243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq858582 : ∀ X0 : G, (σ (k (M.op x x) y)) = (σ (M.op (M.op (M.op x x) X0) (M.op x x))) ∨ y = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq253832 (M.op x x) x (M.op X0 y)
       have i₂ := eq852566 X0
       grind)
    | exact superpose eq852566 eq253832
    | exact resolve eq253832 eq852566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253832 eq852566
  have eq858762 : (σ x) = (σ (k (M.op x x) y)) ∨ y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq858582 x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq858582
    | exact resolve eq858582 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858582
  have eq929483 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ y = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq503 (M.op x x) y X0
       have i₂ := eq858762
       grind)
    | exact superpose eq858762 eq503
    | (have j0 := eq503 (M.op x x) y x
       grind)
    | exact resolve eq503 eq858762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq858762
  have eq930164 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) y)) ∨ (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq929483 x
       have i₂ := eq382630 y x
       grind)
    | exact superpose eq382630 eq929483
    | exact resolve eq929483 eq382630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929483
  have eq930249 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq930164
       have i₂ := eq852545 y
       grind)
    | exact superpose eq852545 eq930164
    | exact resolve eq930164 eq852545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930164
  have eq930275 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ y = (M.op (M.op x x) y) := by
    first
    | (have r₁ := eq930249
       have r₂ := eq16
       grind)
    | exact resolve eq930249 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930249
  have eq1187293 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (M.op (σ (M.op x x)) X1) (σ (M.op x x))) (σ y)) ∨ y = (M.op (M.op x x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (σ (M.op x x)) X1 (σ y) x
       have i₂ := eq930275
       grind)
    | exact superpose eq930275 eq95
    | exact resolve eq95 eq930275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq930275
  have eq1187661 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq1187293 X0 x
       have i₂ := eq377733 x x
       grind)
    | exact superpose eq377733 eq1187293
    | exact resolve eq1187293 eq377733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377733 eq1187293
  have eq1187830 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) y)) ∨ y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1187661 x
       have i₂ := eq382630 y x
       grind)
    | exact superpose eq382630 eq1187661
    | exact resolve eq1187661 eq382630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187661
  have eq1187922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1187830
       have i₂ := eq852545 y
       grind)
    | exact superpose eq852545 eq1187830
    | exact resolve eq1187830 eq852545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187830
  have eq1187949 : y = (M.op (M.op x x) y) := by
    first
    | (have r₁ := eq1187922
       have r₂ := eq16
       grind)
    | exact resolve eq1187922 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187922
  have eq1187990 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq408 x y
       have i₂ := eq1187949
       grind)
    | exact superpose eq1187949 eq408
    | exact resolve eq408 eq1187949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq1187949
  have eq1529167 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26714 X0 X1
       have i₂ := eq382630 X0 (σ X0)
       grind)
    | exact superpose eq382630 eq26714
    | (have j0 := eq26714 X0 X1
       grind)
    | exact resolve eq26714 eq382630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26714
  have eq1529779 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) y)) ∨ (σ y) = (M.op (σ (M.op X0 x)) (σ y)) ∨ y = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq1529167 y (M.op X0 x)
       have i₂ := eq852563 X0
       grind)
    | exact superpose eq852563 eq1529167
    | (have j0 := eq1529167 y (M.op X0 x)
       grind)
    | exact resolve eq1529167 eq852563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852563
  have eq1529904 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1529167 y x
       have i₂ := eq852243
       grind)
    | exact superpose eq852243 eq1529167
    | (have j0 := eq1529167 y x
       grind)
    | exact resolve eq1529167 eq852243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529167
  have eq1531942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1529904
       have i₂ := eq852545 y
       grind)
    | exact superpose eq852545 eq1529904
    | exact resolve eq1529904 eq852545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529904
  have eq1532031 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op X0 x)) (σ y)) ∨ y = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq1529779 X0
       have i₂ := eq852545 y
       grind)
    | exact superpose eq852545 eq1529779
    | (have j0 := eq1529779 X0
       grind)
    | exact resolve eq1529779 eq852545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529779
  have eq1532696 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1531942
       have r₂ := eq16
       grind)
    | exact resolve eq1531942 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531942
  have eq1532750 : ∀ X0 : G, (σ y) = (M.op (σ (M.op X0 x)) (σ y)) ∨ y = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have j0 := eq1532031 X0
       grind)
    | (have r₁ := eq1532031 X0
       have r₂ := eq16
       grind)
    | exact resolve eq1532031 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532031
  have eq1533896 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1532696
       grind)
    | exact superpose eq1532696 eq16
    | exact resolve eq16 eq1532696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1533943 : (M.op (σ y) (σ x)) = (σ (M.op (M.op x x) x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq382630 x (σ y)
       have i₂ := eq1532696
       grind)
    | exact superpose eq1532696 eq382630
    | exact resolve eq382630 eq1532696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532696
  have eq1540490 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op (M.op (M.op x x) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1532750 (M.op x x)
       have i₂ := eq1533943
       grind)
    | exact superpose eq1533943 eq1532750
    | (have j0 := eq1532750 (M.op x x)
       grind)
    | exact resolve eq1532750 eq1533943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532750 eq1533943
  have eq1541227 : (σ y) = (σ (M.op (M.op y y) y)) ∨ y = (M.op (M.op (M.op x x) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1540490
       have i₂ := eq382630 y (σ x)
       grind)
    | exact superpose eq382630 eq1540490
    | exact resolve eq1540490 eq382630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382630 eq1540490
  have eq1541292 : (σ (M.op x y)) = (σ y) ∨ y = (M.op (M.op (M.op x x) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1541227
       have i₂ := eq852545 y
       grind)
    | exact superpose eq852545 eq1541227
    | exact resolve eq1541227 eq852545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541227
  have eq1541306 : y = (M.op (M.op (M.op x x) x) y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1541292
       have r₂ := eq1533896
       grind)
    | exact resolve eq1541292 eq1533896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533896 eq1541292
  have eq1541417 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op (M.op (M.op (M.op x x) x) (M.op (M.op x x) x)) y) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq885 (M.op (M.op x x) x) y x
       have i₂ := eq1541306
       grind)
    | exact superpose eq1541306 eq885
    | exact resolve eq885 eq1541306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq1541306
  have eq1541820 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1541417 X0
       have i₂ := eq9 x x (M.op x x)
       grind)
    | exact superpose eq9 eq1541417
    | exact resolve eq1541417 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541417
  have eq1542021 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1541820 X0
       have i₂ := eq1187990
       grind)
    | exact superpose eq1187990 eq1541820
    | exact resolve eq1541820 eq1187990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187990 eq1541820
  have eq1542090 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1542021 x
       have i₂ := eq852545 x
       grind)
    | exact superpose eq852545 eq1542021
    | exact resolve eq1542021 eq852545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542021
  have eq1542091 : y = (M.op x y) := by grind
  clear eq1542090
  have eq1542260 : ∀ X0 : G, x ≠ (M.op y x) ∨ (k X0 (M.op y x)) = (M.op (M.op y x) X0) := by
    intro X0
    first
    | (have i₁ := eq767 x y x
       have i₂ := eq1542091
       grind)
    | exact superpose eq1542091 eq767
    | exact resolve eq767 eq1542091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq1542091
  have eq1542698 : ∀ X0 : G, (k X0 (M.op y x)) = (M.op (M.op y x) X0) := by
    intro X0
    first
    | (have j0 := eq1542260 X0
       grind)
    | (have r₁ := eq1542260 X0
       have r₂ := eq852243
       grind)
    | exact resolve eq1542260 eq852243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542260
  have eq1542813 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1542698 X0
       have i₂ := eq852243
       grind)
    | exact superpose eq852243 eq1542698
    | exact resolve eq1542698 eq852243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852243 eq1542698
  have eq1557302 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq492
       have i₂ := eq1542813 y
       grind)
    | exact superpose eq1542813 eq492
    | exact resolve eq492 eq1542813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq1542813
  have eq1557310 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1557302
  have eq1572703 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq382631 y X0 (σ x)
       have i₂ := eq1557310
       grind)
    | exact superpose eq1557310 eq382631
    | exact resolve eq382631 eq1557310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382631 eq1557310
  have eq1573303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1572703 x
       have i₂ := eq852545 x
       grind)
    | exact superpose eq852545 eq1572703
    | exact resolve eq1572703 eq852545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852545 eq1572703
  have eq1573588 : False := by grind
  exact eq1573588

/-- `Equation2055`: `x = ((x ◇ y) ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyy_pyy_pxy_Equation2055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2055 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2055.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq41 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq28
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X0) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X1) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) X0) (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X2
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) X1
       have i₂ := eq53 X1 X0 X2
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq53 X0 (M.op (M.op X0 X0) X0) x
       have i₂ := eq57 X0 x X0
       grind)
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x)
       have i₂ := eq57 X0 x x
       grind)
    | exact superpose eq57 eq52
    | exact resolve eq52 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq94 X0
       have i₂ := eq57 X0 X0 X0
       grind)
    | exact superpose eq57 eq94
    | exact resolve eq94 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq99 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq12
    | (have j0 := eq12 (M.op (M.op X0 X0) X0) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) X0) X0
       have r₂ := eq97 X0
       grind)
    | exact resolve eq12 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq104 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq112 : ∀ X0 : G, (k (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 (M.op (M.op x x) x)
       have i₂ := eq57 x x x
       grind)
    | exact superpose eq57 eq109
    | exact resolve eq109 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq115 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (k (M.op X1 X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 (M.op X1 X2) (M.op (M.op X0 X1) X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq99
    | (have j0 := eq99 (M.op X1 X2) (M.op (M.op X0 X1) X0)
       grind)
    | (have r₁ := eq99 (M.op X1 X2) (M.op (M.op (M.op X1 X2) X1) (M.op X1 X2))
       have r₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq99 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq99
    | (have j0 := eq99 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq99 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq97 X0
       grind)
    | exact resolve eq99 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq119 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq57 X0 X0 X0
       grind)
    | exact superpose eq57 eq120
    | exact resolve eq120 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq165 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) X0) X0 X2 x
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq51
    | exact resolve eq51 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq390 X0 X1 X2
       have i₂ := eq9 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq9 eq390
    | exact resolve eq390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq544 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq9
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq560 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq9 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq9 eq544
    | exact resolve eq544 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq563 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq560 X0 x
       have i₂ := eq52 X0 x
       grind)
    | exact superpose eq52 eq560
    | exact resolve eq560 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq567 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X0 X0 X1 X2
       have i₂ := eq563 X0
       grind)
    | exact superpose eq563 eq51
    | exact resolve eq51 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1))) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq115 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq593 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq424 X0 X1 X2
       have i₂ := eq563 X0
       grind)
    | exact superpose eq563 eq424
    | exact resolve eq424 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq603 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq593 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq593
    | exact resolve eq593 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X0 X1 X2 X3
       have i₂ := eq593 X0 X1 X0
       grind)
    | exact superpose eq593 eq51
    | exact resolve eq51 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X1) X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq593 X0 X1 X2
       grind)
    | exact superpose eq593 eq9
    | exact resolve eq9 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq563 X0
       grind)
    | exact superpose eq563 eq112
    | exact resolve eq112 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq694 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq160 x y
       grind)
    | exact superpose eq160 eq16
    | (have j1 := eq160 x y
       grind)
    | exact resolve eq16 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq679 (M.op (M.op x x) x)
       have i₂ := eq57 x x x
       grind)
    | exact superpose eq57 eq679
    | exact resolve eq679 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq749 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq739 X0
       have i₂ := eq563 X0
       grind)
    | exact superpose eq563 eq739
    | exact resolve eq739 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq739
  have eq865 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X1) X2) X3
       have i₂ := eq567 X0 X1 X2
       grind)
    | exact superpose eq567 eq9
    | exact resolve eq9 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq882 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq865 X0 X1 X2 X3
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq865
    | exact resolve eq865 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq926 : ∀ X0 X3 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq882 (M.op X0 X0) X0 (M.op (M.op X0 x) x) X3
       have i₂ := eq57 X0 x x
       grind)
    | exact superpose eq57 eq882
    | exact resolve eq882 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq963 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq926 X0 X3
       have i₂ := eq603 X0 X0
       grind)
    | exact superpose eq603 eq926
    | exact resolve eq926 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq1023 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq121 (M.op X0 X0)
       have i₂ := eq963 X0 X0
       grind)
    | exact superpose eq963 eq121
    | exact resolve eq121 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1033 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1023 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq1023
    | exact resolve eq1023 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1067 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq1033 (σ X0)
       grind)
    | exact superpose eq1033 eq22
    | exact resolve eq22 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X1 (M.op X0 X0) X0 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq613
    | exact resolve eq613 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq613 X1 (M.op X0 X2) X0 (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq613
    | exact resolve eq613 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq1368 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1224 X1 (M.op (M.op X0 X1) X0)
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq1224
    | exact resolve eq1224 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1386 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X2
       have i₂ := eq1224 X1 X0
       grind)
    | exact superpose eq1224 eq9
    | exact resolve eq9 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1459 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1368 X0 X1
       have i₂ := eq603 (M.op X0 X1) X0
       grind)
    | exact superpose eq603 eq1368
    | exact resolve eq1368 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368
  have eq1488 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1459 X0 X1
       have i₂ := eq593 X0 X1 X0
       grind)
    | exact superpose eq593 eq1459
    | exact resolve eq1459 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1542 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 X2
       have i₂ := eq1227 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq1227 eq53
    | exact resolve eq53 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1546 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 X2) X3
       have i₂ := eq1227 X1 X0 X2
       grind)
    | exact superpose eq1227 eq9
    | exact resolve eq9 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1551 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 (M.op X0 X1)
       have i₂ := eq1227 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq1227 eq121
    | exact resolve eq121 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq1605 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1551 X0 X1
       have i₂ := eq603 X0 X1
       grind)
    | exact superpose eq603 eq1551
    | exact resolve eq1551 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1681 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1542 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq57 X0 X0 X0
       grind)
    | exact superpose eq57 eq1542
    | exact resolve eq1542 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1841 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1386 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq57 X0 X0 X0
       grind)
    | exact superpose eq57 eq1386
    | exact resolve eq1386 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq2045 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1546 (M.op (M.op X0 X0) X0) X1 X2 X3
       have i₂ := eq57 X0 X0 X0
       grind)
    | exact superpose eq57 eq1546
    | exact resolve eq1546 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq2530 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X0
       have i₂ := eq1681 X0 X1 X2
       grind)
    | exact superpose eq1681 eq97
    | exact resolve eq97 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2592 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op X1 X2))) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X2)) X1 X3
       have i₂ := eq1681 X0 X1 X2
       grind)
    | exact superpose eq1681 eq9
    | exact resolve eq9 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2615 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X3)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op (M.op X1 X2) X1) X3))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (M.op X0 (M.op (M.op (M.op X1 X2) X1) X3)) X2
       have i₂ := eq1681 X0 (M.op (M.op X1 X2) X1) X3
       grind)
    | exact superpose eq1681 eq53
    | exact resolve eq53 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq2621 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2615 X0 X1 X2 X3
       have i₂ := eq9 X0 X0 (M.op (M.op (M.op X1 X2) X1) X3)
       grind)
    | exact superpose eq9 eq2615
    | exact resolve eq2615 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq2641 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2592 X0 X1 X2 X3
       have i₂ := eq9 X0 X0 (M.op X1 X2)
       grind)
    | exact superpose eq9 eq2592
    | exact resolve eq2592 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2769 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X2) X0)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2530 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq2530
    | exact resolve eq2530 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530
  have eq5004 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2769 X1 X0 X2
       have i₂ := eq2641 (M.op X0 X1) (M.op X1 X2) X1 X3
       grind)
    | (have i₁ := eq2769 X1 X0 X2
       have i₂ := eq2641 (M.op X0 X1) (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq2641 eq2769
    | exact resolve eq2769 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2641
  have eq5934 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq603 (M.op X0 X1) X0
       grind)
    | exact superpose eq603 eq54
    | exact resolve eq54 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq7839 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq603 X0 X1
       grind)
    | exact superpose eq603 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | (have r₁ := eq69 (M.op X0 X1) X0
       have r₂ := eq603 X0 X1
       grind)
    | exact resolve eq69 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq8232 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq614 (M.op (M.op X0 X1) X0) (M.op X1 x) X3 X4
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq614
    | exact resolve eq614 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq8478 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X0 X1)) (M.op (M.op X0 X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8232 X0 X1 X3 X4
       have i₂ := eq1227 (M.op X0 X1) (M.op (M.op X0 X1) X0) X0
       grind)
    | exact superpose eq1227 eq8232
    | exact resolve eq8232 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8232
  have eq8554 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op (M.op X0 X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq8478 X0 X1 X3 X4
       have i₂ := eq2769 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq2769 eq8478
    | exact resolve eq8478 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769 eq8478
  have eq10329 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1488 X0 X1
       have i₂ := eq5934 X0 X1
       grind)
    | exact superpose eq5934 eq1488
    | exact resolve eq1488 eq5934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq12155 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X1) X2)) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X0 X3
       have i₂ := eq1841 X0 X1 X2
       grind)
    | exact superpose eq1841 eq9
    | exact resolve eq9 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq12988 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) (M.op X0 X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X0 X4
       have i₂ := eq2045 X0 X1 X2 X3
       grind)
    | exact superpose eq2045 eq9
    | exact resolve eq9 eq2045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13186 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X1 X2) X3) X4
       have i₂ := eq2045 X0 X1 X2 X3
       grind)
    | exact superpose eq2045 eq9
    | exact resolve eq9 eq2045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq13363 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13186 X0 X1 X2 X3 X4
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq13186
    | exact resolve eq13186 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13186
  have eq14343 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op X0 (τ X1)) (τ X2)) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op X0 (τ X1)) X2
       have i₂ := eq165 X0 X1
       grind)
    | exact superpose eq165 eq28
    | (have j1 := eq165 X0 X1
       grind)
    | exact resolve eq28 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq165
  have eq14354 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op X0 (τ X1)) (τ X2)) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14343 X0 X1 X2
       have i₂ := eq41 X0 X1 X2
       grind)
    | exact superpose eq41 eq14343
    | (have j0 := eq14343 X0 X1 X2
       grind)
    | exact resolve eq14343 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq14343
  have eq17363 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1067 x
       have i₂ := eq160 x x
       grind)
    | exact superpose eq160 eq1067
    | (have j1 := eq160 X0 X0
       grind)
    | exact resolve eq1067 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq1067
  have eq17387 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17363
  have eq17400 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17387 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq17387
    | (have j0 := eq17387 X0
       grind)
    | exact resolve eq17387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17387
  have eq19853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq694
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq694
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq694 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq19854 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq19853
  have eq33292 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X0 X0) (M.op X1 X2))) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X1 X2 X2
       have i₂ := eq1227 (M.op X2 X2) X1 X2
       grind)
    | exact superpose eq1227 eq79
    | exact resolve eq79 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq33293 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33292 X0 X1 X2
       have i₂ := eq603 (M.op X0 X0) (M.op X1 X2)
       grind)
    | exact superpose eq603 eq33292
    | exact resolve eq33292 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33292
  have eq33294 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33293 X0 X1 X2
       have i₂ := eq1227 X1 (M.op X0 X0) X2
       grind)
    | exact superpose eq1227 eq33293
    | exact resolve eq33293 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq33293
  have eq33295 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33294 X0 X1 X2
       have i₂ := eq603 X0 X0
       grind)
    | exact superpose eq603 eq33294
    | exact resolve eq33294 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33294
  have eq33543 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2))) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) (M.op (M.op X0 X1) X2)) (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0 X1 X2
       have i₂ := eq33295 (M.op (M.op X0 X1) X2) (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2))
       grind)
    | exact superpose eq33295 eq51
    | exact resolve eq51 eq33295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33668 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) X2) (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3)) X1
       have i₂ := eq33295 (M.op (M.op X0 X1) X0) X2 X3
       grind)
    | exact superpose eq33295 eq53
    | exact resolve eq53 eq33295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq33295
  have eq33711 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) X2) (M.op X0 X1)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33668 X0 X1 X2 X3
       have i₂ := eq13363 (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) X2) (M.op X0 X1) X0 (M.op (M.op X0 X1) X0) (M.op X2 X3)
       grind)
    | exact superpose eq13363 eq33668
    | exact resolve eq33668 eq13363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33668
  have eq33817 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33543 X0 X1 X2
       have i₂ := eq57 (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq57 eq33543
    | exact resolve eq33543 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq33543
  have eq33965 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33711 X0 X1 X2 X3
       have i₂ := eq12988 (M.op X0 X1) X0 X1 X0 X0
       grind)
    | exact superpose eq12988 eq33711
    | exact resolve eq33711 eq12988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12988 eq33711
  have eq34021 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33817 X0 X1 X2
       have i₂ := eq13363 (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq13363 eq33817
    | exact resolve eq33817 eq13363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13363 eq33817
  have eq34079 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) (M.op X2 X3)) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33965 X0 X1 X2 X3
       have i₂ := eq603 (M.op X0 X1) X0
       grind)
    | exact superpose eq603 eq33965
    | exact resolve eq33965 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33965
  have eq34114 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34021 X0 X1 X2
       have i₂ := eq603 (M.op X0 X1) X2
       grind)
    | exact superpose eq603 eq34021
    | exact resolve eq34021 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34021
  have eq34130 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34079 X0 X1 X2 X3
       have i₂ := eq5934 X0 X1
       grind)
    | exact superpose eq5934 eq34079
    | exact resolve eq34079 eq5934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34079
  have eq36108 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op (M.op (M.op X0 X1) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 X1
       have i₂ := eq5934 X0 X1
       grind)
    | exact superpose eq5934 eq591
    | exact resolve eq591 eq5934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq5934
  have eq36109 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op (M.op X0 X1) X0)) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36108 X0 X1
       have i₂ := eq603 (M.op (M.op X0 X1) X0) X0
       grind)
    | exact superpose eq603 eq36108
    | exact resolve eq36108 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36108
  have eq36110 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36109 X0 X1
       have i₂ := eq1605 X0 X1
       grind)
    | exact superpose eq1605 eq36109
    | exact resolve eq36109 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605 eq36109
  have eq36231 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op (M.op X0 X1) X2))) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op (M.op X0 X1) X2)) (M.op (M.op X0 X1) X2)) (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36110 (M.op (M.op X1 X2) x) (M.op (M.op (M.op (M.op X1 X2) x) X1) (M.op (M.op X1 X2) x))
       have i₂ := eq51 (M.op (M.op X1 X2) x) X1 X2 x
       grind)
    | exact superpose eq51 eq36110
    | exact resolve eq36110 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq36568 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36231 X0 X1 X2
       have i₂ := eq36110 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact superpose eq36110 eq36231
    | exact resolve eq36231 eq36110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36110 eq36231
  have eq36722 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36568 X0 X1 X2
       have i₂ := eq593 (M.op (M.op X0 X1) X2) X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq593 eq36568
    | exact resolve eq36568 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq36568
  have eq36838 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36722 X0 X1 X2
       have i₂ := eq603 (M.op X0 X1) X2
       grind)
    | exact superpose eq603 eq36722
    | exact resolve eq36722 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq36722
  have eq59138 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34114 X0 X1 X2
       have i₂ := eq36838 X0 X1 X2
       grind)
    | exact superpose eq36838 eq34114
    | exact resolve eq34114 eq36838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34114
  have eq116402 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op X2 X3)) = (M.op (M.op (M.op (M.op X0 X1) X2) X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34130 X0 X1 X2 X3
       have i₂ := eq36838 X0 X1 X2
       grind)
    | exact superpose eq36838 eq34130
    | exact resolve eq34130 eq36838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34130 eq36838
  have eq117131 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) X0) (M.op (M.op (M.op X0 X1) X0) X0)) (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X0) X0) (M.op X2 X3) X4
       have i₂ := eq116402 X0 X1 X2 X3
       grind)
    | exact superpose eq116402 eq9
    | exact resolve eq9 eq116402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116402
  have eq117492 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) X0) X0) (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq117131 X0 X1 X2 X3 X4
       have i₂ := eq2621 (M.op (M.op (M.op (M.op X0 X1) X2) X0) X0) X0 X1 X0
       grind)
    | exact superpose eq2621 eq117131
    | exact resolve eq117131 eq2621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621 eq117131
  have eq118253 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq117492 X0 X1 X2 X3 X4
       have i₂ := eq59138 X0 X1 X2
       grind)
    | exact superpose eq59138 eq117492
    | exact resolve eq117492 eq59138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59138 eq117492
  have eq204384 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq19854
       grind)
    | exact superpose eq19854 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19854
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19854
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19854
       grind)
    | exact resolve eq12 eq19854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19854
  have eq204607 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq204384
  have eq204686 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq99 (σ x) (σ y)
       grind)
    | (have r₁ := eq204607
       have r₂ := eq99 (σ x) (σ y)
       grind)
    | (have r₁ := eq204607
       have r₂ := eq99 x y
       grind)
    | (have r₁ := eq204607
       have r₂ := eq99 y x
       grind)
    | exact resolve eq204607 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204607
  have eq204709 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq204686
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq204686
    | exact resolve eq204686 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204686
  have eq265293 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq17400 (τ X0)
       grind)
    | exact superpose eq17400 eq18
    | (have j1 := eq17400 (τ X0)
       grind)
    | exact resolve eq18 eq17400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17400
  have eq265307 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq265293 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq265293
    | (have j0 := eq265293 X0
       grind)
    | exact resolve eq265293 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq265293
  have eq265341 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq265307 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq265307
    | (have j0 := eq265307 X0
       grind)
    | exact resolve eq265307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265307
  have eq265372 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq265341 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq265341
    | (have j0 := eq265341 X0
       grind)
    | exact resolve eq265341 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265341
  have eq265433 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14354 (τ X0) X0 X0
       have i₂ := eq265372 (τ X0)
       grind)
    | exact superpose eq265372 eq14354
    | (have j0 := eq14354 (τ X0) X0 x
       have j1 := eq265372 (τ X0)
       grind)
    | exact resolve eq14354 eq265372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14354 eq265372
  have eq265474 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq265433 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265433
  have eq265501 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq265474 X0
       have i₂ := eq1033 (τ X0)
       grind)
    | exact superpose eq1033 eq265474
    | (have j0 := eq265474 X0
       grind)
    | exact resolve eq265474 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq265474
  have eq265535 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq265501 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq265501 X0
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | exact resolve eq265501 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265501
  have eq265560 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq265535 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq265535
    | exact resolve eq265535 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq265535
  have eq265582 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq265560 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq265560
    | exact resolve eq265560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265560
  have eq266097 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq265582 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq265582
    | exact resolve eq265582 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq265582
  have eq266126 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq266097 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq266097
    | exact resolve eq266097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266097
  have eq266193 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq266126 (σ X0)
       grind)
    | exact superpose eq266126 eq15
    | exact resolve eq15 eq266126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266245 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq266193 X0
       have i₂ := eq266126 X0
       grind)
    | exact superpose eq266126 eq266193
    | exact resolve eq266193 eq266126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266126 eq266193
  have eq268657 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0) (σ X0)
       have i₂ := eq266245 X0
       grind)
    | exact superpose eq266245 eq52
    | exact resolve eq52 eq266245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq268732 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7839 (σ X0) (σ X0)
       have i₂ := eq266245 X0
       grind)
    | exact superpose eq266245 eq7839
    | exact resolve eq7839 eq266245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7839
  have eq268918 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq268732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268732
  have eq268951 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq268918 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq268918
    | exact resolve eq268918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268918
  have eq269018 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq268951 X0
       have i₂ := eq749 X0
       grind)
    | exact superpose eq749 eq268951
    | exact resolve eq268951 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq268951
  have eq1225723 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X2 X3) X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10329 X0 X1
       have i₂ := eq118253 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq118253 eq10329
    | exact resolve eq10329 eq118253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10329 eq118253
  have eq1311861 : (σ (k x y)) = (σ (M.op y y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq204709
       have i₂ := eq266245 y
       grind)
    | exact superpose eq266245 eq204709
    | exact resolve eq204709 eq266245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204709
  have eq1311986 : (k x y) = (τ (σ (M.op y y))) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1311861
       grind)
    | exact superpose eq1311861 eq10
    | exact resolve eq10 eq1311861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311861
  have eq1312497 : (k x y) = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1311986
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq1311986
    | exact resolve eq1311986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311986
  have eq1312553 : (k x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1312497
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq1312497
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1312497 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312497
  have eq1312580 : (k x y) = (M.op y y) := by
    first
    | (have j1 := eq99 x y
       grind)
    | (have r₁ := eq1312553
       have r₂ := eq99 x y
       grind)
    | exact resolve eq1312553 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1312553
  have eq1312609 : (M.op x y) = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1312580
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1312580
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1312580 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312580
  have eq1314554 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op y X1)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq12155 y y x x
       have i₂ := eq1312609
       grind)
    | exact superpose eq1312609 eq12155
    | exact resolve eq12155 eq1312609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12155 eq1312609
  have eq1314981 : ∀ X1 : G, y = (M.op (M.op (M.op x y) x) (M.op y X1)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq1314554 x X1
       have i₂ := eq8554 x y y x
       grind)
    | exact superpose eq8554 eq1314554
    | exact resolve eq1314554 eq8554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8554 eq1314554
  have eq1315100 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1314981 x
       have i₂ := eq9 x y x
       grind)
    | exact superpose eq9 eq1314981
    | exact resolve eq1314981 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314981
  have eq1315545 : ∀ X0 X1 X2 : G, (M.op x x) = (M.op (M.op (M.op y X0) (M.op (M.op X0 X1) X2)) y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1225723 x y X0 X1 X2
       have i₂ := eq1315100
       grind)
    | exact superpose eq1315100 eq1225723
    | exact resolve eq1225723 eq1315100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315555 : y = (M.op x x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1315545 x x x
       have i₂ := eq5004 y x x x
       grind)
    | exact superpose eq5004 eq1315545
    | exact resolve eq1315545 eq5004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315545
  have eq1315840 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq268657 x
       have i₂ := eq1315555
       grind)
    | exact superpose eq1315555 eq268657
    | exact resolve eq268657 eq1315555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268657 eq1315555
  have eq1326688 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1315840
       grind)
    | exact superpose eq1315840 eq16
    | exact resolve eq16 eq1315840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315840
  have eq1327566 : (σ y) ≠ (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1326688
       have i₂ := eq1315100
       grind)
    | exact superpose eq1315100 eq1326688
    | exact resolve eq1326688 eq1315100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315100 eq1326688
  have eq1327567 : (σ y) ≠ (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1327566
  have eq1327568 : x = (M.op y x) ∨ x = y := by grind
  clear eq1327567
  have eq1327959 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op (M.op x X0) (M.op (M.op X0 X1) X2)) x) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1225723 y x X0 X1 X2
       have i₂ := eq1327568
       grind)
    | exact superpose eq1327568 eq1225723
    | exact resolve eq1225723 eq1327568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225723 eq1327568
  have eq1327969 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1327959 x x x
       have i₂ := eq5004 x x x x
       grind)
    | exact superpose eq5004 eq1327959
    | exact resolve eq1327959 eq5004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004 eq1327959
  have eq1328277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq269018 y
       have i₂ := eq1327969
       grind)
    | exact superpose eq1327969 eq269018
    | exact resolve eq269018 eq1327969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269018 eq1327969
  have eq1329007 : x = y := by
    first
    | (have r₁ := eq1328277
       have r₂ := eq16
       grind)
    | exact resolve eq1328277 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328277
  have eq1329112 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1329007
       grind)
    | exact superpose eq1329007 eq16
    | exact resolve eq16 eq1329007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329007
  have eq1329128 : False := by grind
  exact eq1329128

/-- `Equation2055`: `x = ((x ◇ y) ◇ x) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyy_y_pxy_Equation2055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2055 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2055.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X0) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X1) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) X0) (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X2
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) X1
       have i₂ := eq53 X1 X0 X2
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq53 X0 (M.op (M.op X0 X0) X0) x
       have i₂ := eq57 X0 x X0
       grind)
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) X0) (M.op (M.op X0 x) x)
       have i₂ := eq57 X0 x x
       grind)
    | exact superpose eq57 eq52
    | exact resolve eq52 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq94 X0
       have i₂ := eq57 X0 X0 X0
       grind)
    | exact superpose eq57 eq94
    | exact resolve eq94 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq99 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X0 ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op X0 X1) X0) = (k (M.op X1 X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op (M.op X0 X1) X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op (M.op X0 X1) X0)
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op (M.op (M.op X1 X2) X1) (M.op X1 X2))
       have r₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq12
    | (have j0 := eq12 (M.op (M.op X0 X0) X0) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) X0) X0
       have r₂ := eq97 X0
       grind)
    | exact resolve eq12 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq107 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq117 : ∀ X0 : G, (k (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq114 (M.op (M.op x x) x)
       have i₂ := eq57 x x x
       grind)
    | exact superpose eq57 eq114
    | exact resolve eq114 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq218 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 X0) X0) X0 X2 x
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq51
    | exact resolve eq51 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq375 X0 X1 X2
       have i₂ := eq9 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq9 eq375
    | exact resolve eq375 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq9
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq433 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X1
       have i₂ := eq9 X0 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq9 eq418
    | exact resolve eq418 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq436 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq433 X0 x
       have i₂ := eq52 X0 x
       grind)
    | exact superpose eq52 eq433
    | exact resolve eq433 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq465 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq408 X0 X1 X2
       have i₂ := eq436 X0
       grind)
    | exact superpose eq436 eq408
    | exact resolve eq408 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq475 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq465 (M.op X0 X1) X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq465
    | exact resolve eq465 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X0 X1 X2 X3
       have i₂ := eq465 X0 X1 X0
       grind)
    | exact superpose eq465 eq51
    | exact resolve eq51 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X1) X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq465 X0 X1 X2
       grind)
    | exact superpose eq465 eq9
    | exact resolve eq9 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq213 x y
       grind)
    | exact superpose eq213 eq16
    | (have j1 := eq213 x y
       grind)
    | exact resolve eq16 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq213 X0 X1
       grind)
    | exact superpose eq213 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq213 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq213 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq213 X0 X1
       grind)
    | exact resolve eq12 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq213 X0 X1
       grind)
    | exact superpose eq213 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq213 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq213 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq213 X0 X1
       grind)
    | exact resolve eq13 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq213 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq582 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq580 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq588 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq566 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq588 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq588 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq588 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq591 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq565 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq565 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq565 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq565 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq598 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq590
    | (have j0 := eq590 X0 X1
       grind)
    | exact resolve eq590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq599 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq591
    | (have j0 := eq591 X0 X1
       grind)
    | exact resolve eq591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq604 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq582 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq582
    | (have j0 := eq582 (τ X0)
       grind)
    | exact resolve eq582 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq614 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq604 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq604
    | (have j0 := eq604 X0
       grind)
    | exact resolve eq604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq621 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq614
    | (have j0 := eq614 X0
       grind)
    | exact resolve eq614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq654 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq436 X0
       grind)
    | exact superpose eq436 eq117
    | exact resolve eq117 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq655 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq654 (M.op (M.op x x) x)
       have i₂ := eq57 x x x
       grind)
    | exact superpose eq57 eq654
    | exact resolve eq654 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq655 X0
       have i₂ := eq436 X0
       grind)
    | exact superpose eq436 eq655
    | exact resolve eq655 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq927 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1))) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq99 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq928 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq927 X0 X1
       have i₂ := eq465 (M.op X0 X1) X0 (M.op X0 X1)
       grind)
    | exact superpose eq465 eq927
    | (have j0 := eq927 X0 X1
       grind)
    | exact resolve eq927 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq931 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq928 X0 X1
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq928
    | (have j0 := eq928 X0 X1
       grind)
    | exact resolve eq928 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1039 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X1 (M.op X0 X0) X0 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq485
    | exact resolve eq485 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq485 X1 (M.op X0 X2) X0 (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq485
    | exact resolve eq485 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq1170 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X1 (M.op (M.op X0 X1) X0)
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq1039
    | exact resolve eq1039 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1258 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1170 X0 X1
       have i₂ := eq475 (M.op X0 X1) X0
       grind)
    | exact superpose eq475 eq1170
    | exact resolve eq1170 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1285 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1258 X0 X1
       have i₂ := eq465 X0 X1 X0
       grind)
    | exact superpose eq465 eq1258
    | exact resolve eq1258 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1339 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X0 X2
       have i₂ := eq1042 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq1042 eq53
    | exact resolve eq53 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 X2) X3
       have i₂ := eq1042 X1 X0 X2
       grind)
    | exact superpose eq1042 eq9
    | exact resolve eq9 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq1042 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       grind)
    | exact superpose eq1042 eq9
    | exact resolve eq9 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1357 X0 X1
       have i₂ := eq475 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq475 eq1357
    | exact resolve eq1357 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1439 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1399 X0 X1
       have i₂ := eq1042 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq1042 eq1399
    | exact resolve eq1399 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1458 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1439 X0 X1
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq1439
    | exact resolve eq1439 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1475 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1339 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq57 X0 X0 X0
       grind)
    | exact superpose eq57 eq1339
    | exact resolve eq1339 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1824 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1343 (M.op (M.op X0 X0) X0) X1 X2 X3
       have i₂ := eq57 X0 X0 X0
       grind)
    | exact superpose eq57 eq1343
    | exact resolve eq1343 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1343
  have eq2248 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X0
       have i₂ := eq1475 X0 X1 X2
       grind)
    | exact superpose eq1475 eq97
    | exact resolve eq97 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2251 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq654 X0
       have i₂ := eq1475 X0 X1 X2
       grind)
    | exact superpose eq1475 eq654
    | exact resolve eq654 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq2481 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X2) X0)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2248 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq2248
    | exact resolve eq2248 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3901 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq475 (M.op X0 X1) X0
       grind)
    | exact superpose eq475 eq54
    | exact resolve eq54 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq4870 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq3901 X0 X1
       grind)
    | exact superpose eq3901 eq9
    | exact resolve eq9 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op (M.op X0 X1) X2))) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op (M.op X0 X1) X2)) (M.op (M.op X0 X1) X2)) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4870 (M.op (M.op X0 X1) X2) (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op (M.op X0 X1) X2)) X3
       have i₂ := eq51 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq51 eq4870
    | exact resolve eq4870 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq6300 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op (M.op (M.op X0 X1) X2) X0) (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6124 X0 X1 X2 x
       have i₂ := eq4870 (M.op (M.op X0 X1) X2) X0 x
       grind)
    | exact superpose eq4870 eq6124
    | exact resolve eq6124 eq4870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870 eq6124
  have eq6357 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6300 X0 X1 X2
       have i₂ := eq465 (M.op (M.op X0 X1) X2) X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq465 eq6300
    | exact resolve eq6300 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6392 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6357 X0 X1 X2
       have i₂ := eq475 (M.op X0 X1) X2
       grind)
    | exact superpose eq475 eq6357
    | exact resolve eq6357 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6357
  have eq6445 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq486 (M.op (M.op X0 X1) X0) (M.op X1 x) X3 X4
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq486
    | exact resolve eq486 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq6673 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X0 X1)) (M.op (M.op X0 X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq6445 X0 X1 X3 X4
       have i₂ := eq1042 (M.op X0 X1) (M.op (M.op X0 X1) X0) X0
       grind)
    | exact superpose eq1042 eq6445
    | exact resolve eq6445 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6445
  have eq6746 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op (M.op X0 X3) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq6673 X0 X1 X3 X4
       have i₂ := eq2481 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq2481 eq6673
    | exact resolve eq6673 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6673
  have eq8202 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1285 X0 X1
       have i₂ := eq3901 X0 X1
       grind)
    | exact superpose eq3901 eq1285
    | exact resolve eq1285 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq8203 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | (have r₁ := eq69 (M.op X0 X1) X0
       have r₂ := eq475 X0 X1
       grind)
    | exact resolve eq69 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq10578 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) (M.op X0 X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X0 X4
       have i₂ := eq1824 X0 X1 X2 X3
       grind)
    | exact superpose eq1824 eq9
    | exact resolve eq9 eq1824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10746 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X1 X2) X3) X4
       have i₂ := eq1824 X0 X1 X2 X3
       grind)
    | exact superpose eq1824 eq9
    | exact resolve eq9 eq1824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq10897 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10746 X0 X1 X2 X3 X4
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq10746
    | exact resolve eq10746 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10746
  have eq14080 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq598 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq598
    | (have j0 := eq598 (τ X0) (τ X1)
       grind)
    | exact resolve eq598 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq14094 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14080 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq14080
    | (have j0 := eq14080 X0 X1
       grind)
    | exact resolve eq14080 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14080
  have eq14103 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14094 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14094
    | (have j0 := eq14094 X0 X1
       grind)
    | exact resolve eq14094 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14094
  have eq14110 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14103 X0 X1
       have i₂ := eq17 X1 (τ X0)
       grind)
    | exact superpose eq17 eq14103
    | (have j0 := eq14103 X0 X1
       grind)
    | exact resolve eq14103 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq14103
  have eq14111 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14110 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14110
    | (have j0 := eq14110 X0 X1
       grind)
    | exact resolve eq14110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14110
  have eq14112 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14111 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14111
    | (have j0 := eq14111 X0 X1
       grind)
    | exact resolve eq14111 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14111
  have eq14113 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14112 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14112
    | (have j0 := eq14112 X0 X1
       grind)
    | exact resolve eq14112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14112
  have eq17819 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq581 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq581
    | (have j0 := eq581 (τ X0) (τ X1)
       grind)
    | exact resolve eq581 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq17833 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17819 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq17819
    | (have j0 := eq17819 X0 X1
       grind)
    | exact resolve eq17819 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17819
  have eq17840 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17833 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17833
    | (have j0 := eq17833 X0 X1
       grind)
    | exact resolve eq17833 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17833
  have eq17844 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17840 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17840
    | (have j0 := eq17840 X0 X1
       grind)
    | exact resolve eq17840 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840
  have eq17845 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17844 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17844
    | (have j0 := eq17844 X0 X1
       grind)
    | exact resolve eq17844 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17844
  have eq17846 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17845 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17845
    | (have j0 := eq17845 X0 X1
       grind)
    | exact resolve eq17845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17845
  have eq17847 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17846 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17846
    | (have j0 := eq17846 X0 X1
       grind)
    | exact resolve eq17846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17846
  have eq26345 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq562
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq562
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq562 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq26346 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq26345
  have eq26363 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq599 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq599
    | (have j0 := eq599 (τ X0) (τ X1)
       grind)
    | exact resolve eq599 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq599
  have eq26377 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26363 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq26363
    | (have j0 := eq26363 X0 X1
       grind)
    | exact resolve eq26363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26363
  have eq26381 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26377 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq26377
    | (have j0 := eq26377 X0 X1
       grind)
    | exact resolve eq26377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26377
  have eq26385 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26381 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26381
    | (have j0 := eq26381 X0 X1
       grind)
    | exact resolve eq26381 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26381
  have eq26386 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26385 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq26385
    | (have j0 := eq26385 X0 X1
       grind)
    | exact resolve eq26385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26385
  have eq26387 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26386 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26386
    | (have j0 := eq26386 X0 X1
       grind)
    | exact resolve eq26386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26386
  have eq26388 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26387 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq26387
    | (have j0 := eq26387 X0 X1
       grind)
    | exact resolve eq26387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26387
  have eq29026 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X0 X0) (M.op X1 X2))) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X1 X2 X2
       have i₂ := eq1042 (M.op X2 X2) X1 X2
       grind)
    | exact superpose eq1042 eq79
    | exact resolve eq79 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq29027 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29026 X0 X1 X2
       have i₂ := eq475 (M.op X0 X0) (M.op X1 X2)
       grind)
    | exact superpose eq475 eq29026
    | exact resolve eq29026 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29026
  have eq29028 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29027 X0 X1 X2
       have i₂ := eq1042 X1 (M.op X0 X0) X2
       grind)
    | exact superpose eq1042 eq29027
    | exact resolve eq29027 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29027
  have eq29029 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29028 X0 X1 X2
       have i₂ := eq475 X0 X0
       grind)
    | exact superpose eq475 eq29028
    | exact resolve eq29028 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29028
  have eq29070 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) X1) = (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X0 (M.op (M.op X2 X3) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29029 X1 (M.op (M.op X0 (M.op (M.op X2 X3) X2)) X0) X2
       have i₂ := eq53 X2 X0 X3
       grind)
    | exact superpose eq53 eq29029
    | exact resolve eq29029 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29373 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) X2) (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3)) X1
       have i₂ := eq29029 (M.op (M.op X0 X1) X0) X2 X3
       grind)
    | exact superpose eq29029 eq53
    | exact resolve eq53 eq29029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq29412 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) X2) (M.op X0 X1)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29373 X0 X1 X2 X3
       have i₂ := eq10897 (M.op (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) X2) (M.op X0 X1) X0 (M.op (M.op X0 X1) X0) (M.op X2 X3)
       grind)
    | exact superpose eq10897 eq29373
    | exact resolve eq29373 eq10897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29373
  have eq29602 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) X1) = (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X0 X0) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29070 X0 X1 X2 X3
       have i₂ := eq1042 (M.op X2 X3) X0 X2
       grind)
    | exact superpose eq1042 eq29070
    | exact resolve eq29070 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq29070
  have eq29651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29412 X0 X1 X2 X3
       have i₂ := eq10578 (M.op X0 X1) X0 X1 X0 X0
       grind)
    | exact superpose eq10578 eq29412
    | exact resolve eq29412 eq10578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10578 eq29412
  have eq29756 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) (M.op X2 X3)) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29651 X0 X1 X2 X3
       have i₂ := eq475 (M.op X0 X1) X0
       grind)
    | exact superpose eq475 eq29651
    | exact resolve eq29651 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29651
  have eq29800 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) = (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29756 X0 X1 X2 X3
       have i₂ := eq3901 X0 X1
       grind)
    | exact superpose eq3901 eq29756
    | exact resolve eq29756 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29756
  have eq36232 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) X0) ∨ (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq931 X0 X1
       have i₂ := eq3901 X0 X1
       grind)
    | exact superpose eq3901 eq931
    | (have j0 := eq931 X0 X1
       grind)
    | exact resolve eq931 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq36233 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (k (M.op X0 X1) (M.op (M.op (M.op X0 X1) X0) X0)) ∨ (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq36232 X0 X1
       have i₂ := eq3901 X0 X1
       grind)
    | exact superpose eq3901 eq36232
    | (have j0 := eq36232 X0 X1
       grind)
    | exact resolve eq36232 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901 eq36232
  have eq36321 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X0) = (k (M.op X0 X0) (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X0)) ∨ (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36233 X0 X0
       have i₂ := eq1475 X0 X1 X2
       grind)
    | exact superpose eq1475 eq36233
    | exact resolve eq36233 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq36233
  have eq36426 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36321 X0 X1 X2
       have i₂ := eq2248 X0 X1 X2
       grind)
    | exact superpose eq2248 eq36321
    | (have j0 := eq36321 X0 X1 X2
       grind)
    | exact resolve eq36321 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36321
  have eq36507 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36426 X0 X1 X2
       have i₂ := eq2248 X0 X1 X2
       grind)
    | exact superpose eq2248 eq36426
    | (have j0 := eq36426 X0 X1 X2
       grind)
    | exact resolve eq36426 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36426
  have eq47245 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2251 X0 x x
       have i₂ := eq36507 X0 x x
       grind)
    | exact superpose eq36507 eq2251
    | (have j1 := eq36507 X0 x x
       grind)
    | exact resolve eq2251 eq36507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251 eq36507
  have eq47454 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq47245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47245
  have eq48131 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq47454 (σ X0)
       grind)
    | exact superpose eq47454 eq22
    | exact resolve eq22 eq47454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq48134 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq47454 (τ X0)
       grind)
    | exact superpose eq47454 eq18
    | exact resolve eq18 eq47454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq47454
  have eq48151 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48134 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48134
    | exact resolve eq48134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48134
  have eq48154 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48131 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48131
    | exact resolve eq48131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48131
  have eq48181 : ∀ X0 : G, (k (k (σ (τ X0)) X0) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq48151 X0
       have i₂ := eq218 (τ X0) X0
       grind)
    | exact superpose eq218 eq48151
    | (have j1 := eq218 (τ X0) X0
       grind)
    | exact resolve eq48151 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq48219 : ∀ X0 : G, (k (k (σ (τ X0)) X0) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq48181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48181
  have eq48236 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48219 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48219
    | (have j0 := eq48219 X0
       grind)
    | exact resolve eq48219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48219
  have eq49016 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48151 X0
       have i₂ := eq48236 X0
       grind)
    | exact superpose eq48236 eq48151
    | (have j1 := eq48236 X0
       grind)
    | exact resolve eq48151 eq48236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48151 eq48236
  have eq49230 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49016 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49016
    | (have j0 := eq49016 X0
       grind)
    | exact resolve eq49016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49016
  have eq59715 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26388 (k X0 X0) X0
       have i₂ := eq49230 X0
       grind)
    | exact superpose eq49230 eq26388
    | (have j0 := eq26388 X0 X0
       have j1 := eq49230 X0
       grind)
    | (have r₁ := eq26388 (k X0 X0) X0
       have r₂ := eq49230 X0
       grind)
    | (have r₁ := eq26388 X0 X0
       have r₂ := eq49230 X0
       grind)
    | exact resolve eq26388 eq49230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26388 eq49230
  have eq59719 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq59715 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59715
  have eq59738 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq59719 X0
       have j1 := eq621 X0
       grind)
    | (have r₁ := eq59719 X0
       have r₂ := eq621 X0
       grind)
    | exact resolve eq59719 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq59719
  have eq59756 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 (k X0 X0)
       have i₂ := eq59738 X0
       grind)
    | exact superpose eq59738 eq52
    | (have j1 := eq59738 X0
       grind)
    | exact resolve eq52 eq59738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60035 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59738 X0
       have i₂ := eq59756 X0
       grind)
    | exact superpose eq59756 eq59738
    | (have j0 := eq59738 X0
       have j1 := eq59756 X0
       grind)
    | exact resolve eq59738 eq59756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59738 eq59756
  have eq60215 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq60035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60035
  have eq60247 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq60215 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq60215 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq60215 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60215
  have eq60318 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq60247 (σ X0)
       grind)
    | exact superpose eq60247 eq15
    | exact resolve eq15 eq60247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60356 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60318 X0
       have i₂ := eq60247 X0
       grind)
    | exact superpose eq60247 eq60318
    | exact resolve eq60318 eq60247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60247 eq60318
  have eq60802 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0) (σ X0)
       have i₂ := eq60356 X0
       grind)
    | exact superpose eq60356 eq52
    | exact resolve eq52 eq60356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq60865 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8203 (σ X0) (σ X0)
       have i₂ := eq60356 X0
       grind)
    | exact superpose eq60356 eq8203
    | exact resolve eq8203 eq60356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8203 eq60356
  have eq60913 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq60865 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60865
  have eq60925 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq60913 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq60913
    | exact resolve eq60913 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60913
  have eq60972 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq60925 X0
       have i₂ := eq665 X0
       grind)
    | exact superpose eq665 eq60925
    | exact resolve eq60925 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq60925
  have eq77746 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) X2) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X1)) (M.op X2 X3)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29029 (M.op (M.op (M.op X2 X3) (M.op X2 X3)) (M.op X2 X3)) X1 X2
       have i₂ := eq29602 (M.op X2 X3) (M.op X2 X3) X2 X3
       grind)
    | exact superpose eq29602 eq29029
    | exact resolve eq29029 eq29602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29029 eq29602
  have eq78054 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) X2) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X1)) (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77746 X0 X1 X2 X3
       have i₂ := eq10897 (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) (M.op X0 X1)) (M.op X2 X3)) X0 X1 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq10897 eq77746
    | exact resolve eq77746 eq10897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10897 eq77746
  have eq78413 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) X2) = (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq78054 X0 X1 X2 X3
       have i₂ := eq97 (M.op X0 X1)
       grind)
    | exact superpose eq97 eq78054
    | exact resolve eq78054 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq78054
  have eq78589 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) = (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq78413 X0 X1 X2 X3
       have i₂ := eq436 (M.op X0 X1)
       grind)
    | exact superpose eq436 eq78413
    | exact resolve eq78413 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq78413
  have eq78688 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq78589 X0 X1 X2 X3
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq78589
    | exact resolve eq78589 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78589
  have eq86450 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X0) (M.op X2 X3)) = (M.op (M.op (M.op (M.op X0 X1) X2) X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29800 X0 X1 X2 X3
       have i₂ := eq6392 X0 X1 X2
       grind)
    | exact superpose eq6392 eq29800
    | exact resolve eq29800 eq6392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29800
  have eq87067 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) X0)) X0) X0) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1339 (M.op (M.op (M.op X0 X1) X0) X0) X2 X3
       have i₂ := eq86450 X0 X1 (M.op (M.op X0 X1) X0) X0
       grind)
    | exact superpose eq86450 eq1339
    | exact resolve eq1339 eq86450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq86450
  have eq87478 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X0) X0) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87067 X0 X1 X2 X3
       have i₂ := eq6746 X0 X1 X1 X0
       grind)
    | exact superpose eq6746 eq87067
    | exact resolve eq87067 eq6746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87067
  have eq88069 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87478 X0 X1 X2 X3
       have i₂ := eq1458 X0 X1
       grind)
    | exact superpose eq1458 eq87478
    | exact resolve eq87478 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458 eq87478
  have eq98458 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq26346
       grind)
    | exact superpose eq26346 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26346
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq26346
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq26346
       grind)
    | exact resolve eq13 eq26346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26346
  have eq98586 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq98458
  have eq98587 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq98586
  have eq98645 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98587
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq98587
    | exact resolve eq98587 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98587
  have eq518460 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8202 (M.op X0 X1) X2
       have i₂ := eq78688 (M.op X0 X1) X2 X0 X1
       grind)
    | exact superpose eq78688 eq8202
    | exact resolve eq8202 eq78688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78688
  have eq519610 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq518460 X0 X1 X2
       have i₂ := eq6392 X0 X1 X2
       grind)
    | exact superpose eq6392 eq518460
    | exact resolve eq518460 eq6392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392 eq518460
  have eq520424 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq519610 X0 X1 X2
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq519610
    | exact resolve eq519610 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq519610
  have eq704790 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X2) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8202 X0 X1
       have i₂ := eq88069 X0 X1 X2 X3
       grind)
    | exact superpose eq88069 eq8202
    | exact resolve eq8202 eq88069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8202 eq88069
  have eq712360 : ∀ X0 X1 X2 X3 : G, (k (τ (M.op (M.op (M.op (M.op (σ X0) X1) (M.op X2 X3)) X2) X1)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq48154 X0
       have i₂ := eq704790 (σ X0) X1 X2 X3
       grind)
    | exact superpose eq704790 eq48154
    | exact resolve eq48154 eq704790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48154 eq704790
  have eq726844 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X3) (M.op (M.op X0 X1) X0)) (M.op (M.op X0 X1) X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq520424 (M.op (M.op X0 X1) X0) (M.op X1 x) x
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq520424
    | exact resolve eq520424 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520424
  have eq729254 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op (M.op X0 X3) X0) (M.op (M.op X0 X1) X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq726844 X0 X1 X3
       have i₂ := eq6746 X0 X3 X1 X0
       grind)
    | exact superpose eq6746 eq726844
    | exact resolve eq726844 eq6746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746 eq726844
  have eq730052 : ∀ X0 X1 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X3) X0) (M.op (M.op X0 X1) X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq729254 X0 X1 X3
       have i₂ := eq465 X0 X1 X0
       grind)
    | exact superpose eq465 eq729254
    | exact resolve eq729254 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq729254
  have eq2702037 : ∀ X0 X1 : G, y = (k (τ (M.op (M.op (M.op (σ x) (M.op X0 X1)) X0) (σ x))) y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq712360 y (σ x) X0 X1
       have i₂ := eq98645
       grind)
    | exact superpose eq98645 eq712360
    | exact resolve eq712360 eq98645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98645 eq712360
  have eq2702848 : y = (k (τ (σ x)) y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2702037 x x
       have i₂ := eq2248 (σ x) x x
       grind)
    | exact superpose eq2248 eq2702037
    | exact resolve eq2702037 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248 eq2702037
  have eq2702994 : y = (k x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2702848
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2702848
    | exact resolve eq2702848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702848
  have eq2703059 : (σ x) = (σ (k y x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq2702994
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq2702994
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2702994 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702994
  have eq2703233 : (τ (σ x)) = (k y x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq2703059
       grind)
    | exact superpose eq2703059 eq10
    | exact resolve eq10 eq2703059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703059
  have eq2703837 : x = (k y x) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2703233
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2703233
    | exact resolve eq2703233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703233
  have eq2703908 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq14113 y x
       grind)
    | (have r₁ := eq2703837
       have r₂ := eq14113 y x
       grind)
    | (have r₁ := eq2703837
       have r₂ := eq14113 x y
       grind)
    | exact resolve eq2703837 eq14113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14113 eq2703837
  have eq2703978 : y ≠ y ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17847 x y
       have i₂ := eq2703908
       grind)
    | exact superpose eq2703908 eq17847
    | (have j0 := eq17847 x y
       grind)
    | (have r₁ := eq17847 x y
       have r₂ := eq2703908
       grind)
    | exact resolve eq17847 eq2703908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17847 eq2703908
  have eq2704138 : y ≠ y ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2703978
  have eq2704139 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq2704138
  have eq2704664 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y x) (M.op (M.op x X0) x)) y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq730052 x X0 y
       have i₂ := eq2704139
       grind)
    | exact superpose eq2704139 eq730052
    | exact resolve eq730052 eq2704139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2704733 : y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2704664 x
       have i₂ := eq2481 x y x
       grind)
    | exact superpose eq2481 eq2704664
    | exact resolve eq2704664 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704664
  have eq2705329 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq60802 x
       have i₂ := eq2704733
       grind)
    | exact superpose eq2704733 eq60802
    | exact resolve eq60802 eq2704733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60802 eq2704733
  have eq2766205 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2705329
       grind)
    | exact superpose eq2705329 eq16
    | exact resolve eq16 eq2705329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705329
  have eq2767336 : (σ y) ≠ (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2766205
       have i₂ := eq2704139
       grind)
    | exact superpose eq2704139 eq2766205
    | exact resolve eq2766205 eq2704139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704139 eq2766205
  have eq2767337 : (σ y) ≠ (σ y) ∨ x = (M.op y x) := by grind
  clear eq2767336
  have eq2767338 : x = (M.op y x) := by grind
  clear eq2767337
  have eq2767794 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x y) (M.op (M.op y X0) y)) x) := by
    intro X0
    first
    | (have i₁ := eq730052 y X0 x
       have i₂ := eq2767338
       grind)
    | exact superpose eq2767338 eq730052
    | exact resolve eq730052 eq2767338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730052 eq2767338
  have eq2767860 : x = (M.op y y) := by
    first
    | (have i₁ := eq2767794 x
       have i₂ := eq2481 y x x
       grind)
    | exact superpose eq2481 eq2767794
    | exact resolve eq2767794 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2481 eq2767794
  have eq2768490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60972 y
       have i₂ := eq2767860
       grind)
    | exact superpose eq2767860 eq60972
    | exact resolve eq60972 eq2767860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60972 eq2767860
  have eq2769537 : False := by grind
  exact eq2769537

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq69
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq69 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq119
    | exact resolve eq119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq120
       have r₂ := eq27
       grind)
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq27
    | exact resolve eq27 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq73
    | (have r₁ := eq73
       have r₂ := eq125
       grind)
    | exact resolve eq73 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq125
  have eq420 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq419
  have eq423 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq420 eq116
    | exact resolve eq116 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq427 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq423
  have eq432 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq427
       have r₂ := eq127
       grind)
    | exact resolve eq427 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq427
  have eq437 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq432 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq432
       grind)
    | exact resolve eq13 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq444 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq437 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq444 eq116
    | exact resolve eq116 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq444
  have eq532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq529
  have eq537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq532
    | exact resolve eq532 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq539 : x = (M.op x y) := by
    first
    | (have r₁ := eq537
       have r₂ := eq27
       grind)
    | exact resolve eq537 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq541 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq539 eq20
    | exact resolve eq20 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq539 eq72
    | (have r₁ := eq72
       have r₂ := eq539
       grind)
    | exact resolve eq72 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq539
  have eq549 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq544
  have eq556 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq541
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq541
    | exact resolve eq541 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq558 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq556 eq26
    | exact resolve eq26 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq765 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq549
       grind)
    | exact superpose eq549 eq69
    | exact resolve eq69 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq772 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq556 eq765
    | exact resolve eq765 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq774 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq772
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq772
    | exact resolve eq772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq772
  have eq775 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq556 eq774
    | exact resolve eq774 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq778 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq775 eq90
    | (have j0 := eq90 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq90 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq779 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq778
  have eq781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq558 eq779
    | exact resolve eq779 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq784 : x = (M.op x x) := by
    first
    | (have r₁ := eq781
       have r₂ := eq27
       grind)
    | exact resolve eq781 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq791 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq784
       grind)
    | exact superpose eq784 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq784
       grind)
    | exact resolve eq13 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq801 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq791 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq861 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq801 y
       grind)
    | exact superpose eq801 eq69
    | exact resolve eq69 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq801
  have eq867 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq556 eq861
    | exact resolve eq861 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq861
  have eq871 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq867
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq867
    | exact resolve eq867 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq867
  have eq874 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq871
    | exact resolve eq871 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq871
  have eq882 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq874 eq90
    | (have j0 := eq90 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq90 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq874
  have eq883 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq882
  have eq885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq558 eq883
    | exact resolve eq883 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq883
  have eq888 : False := by grind
  exact eq888

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  clear eq18
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq104 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 (M.op X0 X0) X1 x
       have i₂ := eq9 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq9 eq104
    | exact resolve eq104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq143 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq123
    | exact resolve eq123 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq123
  have eq490 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq966 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) X2) ∨ (σ X0) = X2 ∨ (M.op (σ X0) (σ X1)) = (k (σ X0) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq490 X0 X1
       grind)
    | (have i₁ := eq13 (σ X1) X1
       have i₂ := eq490 X1 X1
       grind)
    | exact superpose eq490 eq13
    | (have j0 := eq13 (σ X0) X2
       have j1 := eq490 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq490 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq490 X0 X1
       grind)
    | exact resolve eq13 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq39897 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq966 X0 X1 (σ X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq39898 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq39897 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39897
  have eq39903 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39898 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq39898
    | (have j0 := eq39898 X0 X1
       grind)
    | exact resolve eq39898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39898
  have eq39904 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq39903 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39903
  have eq39916 : ∀ X2 X3 : G, (M.op (σ X2) (σ X3)) = (σ (k X2 X3)) ∨ (σ X2) = (σ X3) := by
    intro X2 X3
    first
    | (have j0 := eq39904 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39904
  have eq39917 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq39916 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39916
  have eq39950 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39917 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq39917
    | (have j0 := eq39917 (τ X0) (τ X1)
       grind)
    | exact resolve eq39917 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq40006 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39950 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq39950
    | (have j0 := eq39950 X0 X1
       grind)
    | exact resolve eq39950 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39950
  have eq40037 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40006 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40006
    | (have j0 := eq40006 X0 X1
       grind)
    | exact resolve eq40006 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40006
  have eq40047 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40037 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq40037
    | (have j0 := eq40037 X0 X1
       grind)
    | exact resolve eq40037 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40037
  have eq40051 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq40047 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq40047
    | (have j0 := eq40047 X0 X1
       grind)
    | exact resolve eq40047 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40047
  have eq40052 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40051 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40051
    | (have j0 := eq40051 X0 X1
       grind)
    | exact resolve eq40051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40051
  have eq40091 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39917 X0 X1
       have i₂ := eq40052 X0 X1
       grind)
    | exact superpose eq40052 eq39917
    | (have j0 := eq39917 X0 X1
       have j1 := eq40052 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq39917 eq40052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39917 eq40052
  have eq1082359 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq40091 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40091
  have eq1083123 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1082359 x y
       grind)
    | exact superpose eq1082359 eq16
    | (have j1 := eq1082359 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1082359 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1082359 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1082359 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1082359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082359
  have eq1083158 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1083123
  have eq1083182 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1083158
       grind)
    | exact superpose eq1083158 eq10
    | exact resolve eq10 eq1083158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083158
  have eq1083323 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1083182
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1083182
    | exact resolve eq1083182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083182
  have eq1083324 : x = y := by grind
  clear eq1083323
  have eq1083325 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1083324
       grind)
    | exact superpose eq1083324 eq16
    | exact resolve eq16 eq1083324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083324
  have eq1083326 : False := by grind
  exact eq1083326

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_y_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq25 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq13 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq126 (σ X1) (σ X0)
       grind)
    | exact superpose eq126 eq15
    | (have j1 := eq126 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq126 X1 X0
       grind)
    | exact superpose eq126 eq141
    | (have j0 := eq141 X0 X1
       have j1 := eq126 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq141 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq141
  have eq242 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq118 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq118 (σ X1) X0
       grind)
    | exact superpose eq118 eq22
    | exact resolve eq22 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118
  have eq1529 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq143 x y
       grind)
    | exact superpose eq143 eq16
    | (have j1 := eq143 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq143 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq143 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq143 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq1533 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1529
  have eq3049 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1533
       grind)
    | exact superpose eq1533 eq10
    | exact resolve eq10 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq3072 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3049
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3049
    | exact resolve eq3049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq3073 : x = y := by grind
  clear eq3072
  have eq3516 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3073
       grind)
    | exact superpose eq3073 eq16
    | exact resolve eq16 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq3517 : False := by grind
  exact eq3517

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    grind
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq146 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq52 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq335 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq335 X0 X1
       grind)
    | exact superpose eq335 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq335 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq335 X1 X1
       grind)
    | exact resolve eq12 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq409 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq109
    | (have j0 := eq109 (σ X0)
       grind)
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq515 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq55 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq55 X2 X2 X2 x
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x
       have i₂ := eq55 X1 X0 y x
       grind)
    | (have i₁ := eq53 (M.op y y)
       have i₂ := eq55 y y y x
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq536 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 x
       have i₂ := eq55 X0 X1 sF3 x
       grind)
    | (have i₁ := eq54 (M.op sF3 sF3)
       have i₂ := eq55 sF3 sF3 sF3 x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq650 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq52 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq52 eq65
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq65
  have eq4223 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq73
       have i₂ := eq369 X0 y
       grind)
    | exact superpose eq369 eq73
    | (have j1 := eq369 X0 y
       grind)
    | exact resolve eq73 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq4237 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq146
       have i₂ := eq369 X0 sF1
       grind)
    | exact superpose eq369 eq146
    | (have j1 := eq369 X0 (σ (M.op x y))
       grind)
    | exact resolve eq146 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq5058 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0
       have i₂ := eq335 X0 (σ X0)
       grind)
    | (have i₁ := eq409 X0
       have i₂ := eq335 (σ X0) X1
       grind)
    | exact superpose eq335 eq409
    | exact resolve eq409 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq6499 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq337 X1 x X2 x
       have i₂ := eq515 X1 x X2 x X0
       grind)
    | exact superpose eq515 eq337
    | exact resolve eq337 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq7013 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6499 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq337 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq337 eq6499
    | exact resolve eq6499 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq6499
  have eq7872 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq27 eq7013
    | (have j0 := eq7013 (σ x) X0 (σ y)
       grind)
    | exact resolve eq7013 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7013
  have eq45322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq45322
    | exact resolve eq45322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45322
  have eq45334 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq45323
       have r₂ := eq28
       grind)
    | exact resolve eq45323 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45323
  have eq45336 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq45334
    | exact resolve eq45334 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45334
  have eq45488 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq45336 eq533
    | exact resolve eq533 eq45336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45336
  have eq45501 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq536 eq45488
    | exact resolve eq45488 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq45488
  have eq45521 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq45501
  have eq45692 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq45521
    | exact resolve eq45521 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45521
  have eq49910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq45692 eq89
    | exact resolve eq89 eq45692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq45692
  have eq49918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq49910
  have eq49920 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq49918
       have r₂ := eq28
       grind)
    | exact resolve eq49918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49918
  have eq50076 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1 y y
       have i₂ := eq49920
       grind)
    | exact superpose eq49920 eq533
    | exact resolve eq533 eq49920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq49920
  have eq50092 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq535 eq50076
    | exact resolve eq50076 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq50076
  have eq50116 : ∀ X0 : G, x = (M.op X0 X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq50092
       have i₂ := eq335 X0 y
       grind)
    | (have i₁ := eq50092
       have i₂ := eq335 y X0
       grind)
    | exact superpose eq335 eq50092
    | exact resolve eq50092 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50126 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq50129 : (σ x) = (M.op (M.op x (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq50092
       grind)
    | exact superpose eq50092 eq54
    | exact resolve eq54 eq50092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq50181 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq650 X0 y
       have i₂ := eq50092
       grind)
    | exact superpose eq50092 eq650
    | exact resolve eq650 eq50092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50208 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4223 y
       have i₂ := eq50092
       grind)
    | exact superpose eq50092 eq4223
    | exact resolve eq4223 eq50092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50092
  have eq50280 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq50208
  have eq50298 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50280
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq50280
    | exact resolve eq50280 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50280
  have eq50303 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50126
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50126
    | exact resolve eq50126 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50126
  have eq51581 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq369 x X1
       have i₂ := eq50116 x
       grind)
    | exact superpose eq50116 eq369
    | exact resolve eq369 eq50116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq50116
  have eq52057 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq50303
       grind)
    | exact superpose eq50303 eq45
    | exact resolve eq45 eq50303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50303
  have eq52075 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq52057
    | exact resolve eq52057 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52057
  have eq60728 : x = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50298
       have i₂ := eq51581 sF3
       grind)
    | exact superpose eq51581 eq50298
    | (have j1 := eq51581 (σ x)
       grind)
    | exact resolve eq50298 eq51581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50298 eq51581
  have eq60729 : (σ x) = (σ y) ∨ x = y ∨ x = (σ x) ∨ x = (σ y) := by grind
  clear eq60728
  have eq60844 : y = (τ (σ x)) ∨ x = y ∨ x = (σ x) ∨ x = (σ y) := by
    first
    | exact superpose eq60729 eq30
    | exact resolve eq30 eq60729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60729
  have eq60984 : x = y ∨ x = y ∨ x = (σ x) ∨ x = (σ y) := by
    first
    | exact superpose eq29 eq60844
    | exact resolve eq60844 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60844
  have eq60985 : x = (σ y) ∨ x = (σ x) ∨ x = y := by grind
  clear eq60984
  have eq61071 : (σ x) = (M.op (M.op x x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq60985 eq50129
    | exact resolve eq50129 eq60985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50129
  have eq61076 : (σ x) = (M.op (M.op x x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) := by grind
  clear eq61071
  have eq61259 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq61076
       have i₂ := eq335 X0 x
       grind)
    | (have i₁ := eq61076
       have i₂ := eq335 x X0
       grind)
    | exact superpose eq335 eq61076
    | exact resolve eq61076 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61274 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = X0 ∨ x = y ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq61076 eq14
    | exact resolve eq14 eq61076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61076
  have eq61633 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq61274 eq7872
    | exact resolve eq7872 eq61274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7872
  have eq61744 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = y ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq61633 eq650
    | exact resolve eq650 eq61633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61850 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq61633 eq61259
    | exact resolve eq61259 eq61633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61259 eq61633
  have eq61872 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) := by grind
  clear eq61850
  have eq62462 : (σ x) = (M.op x (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq60985 eq61872
    | exact resolve eq61872 eq60985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60985 eq61872
  have eq62486 : (σ x) = (M.op x (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) := by grind
  clear eq62462
  have eq62760 : x = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq62486 eq61274
    | exact resolve eq61274 eq62486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61274 eq62486
  have eq62780 : x = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (σ x) := by grind
  clear eq62760
  have eq62782 : ∀ X0 : G, x = (M.op X0 X0) ∨ x = y ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq62780
       have i₂ := eq335 X0 sF2
       grind)
    | (have i₁ := eq62780
       have i₂ := eq335 sF2 x
       grind)
    | exact superpose eq335 eq62780
    | exact resolve eq62780 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62895 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq62780 eq4223
    | exact resolve eq4223 eq62780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223 eq62780
  have eq62988 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (σ x) := by grind
  clear eq62895
  have eq63006 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq62988
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62988
    | exact resolve eq62988 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62988
  have eq65756 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq61744 eq63006
    | exact resolve eq63006 eq61744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61744 eq63006
  have eq65759 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (σ x) := by grind
  clear eq65756
  have eq65984 : x = (σ x) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq65759 eq62782
    | exact resolve eq62782 eq65759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62782 eq65759
  have eq66007 : x = (σ x) ∨ x = y := by grind
  clear eq65984
  have eq66047 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq66007 eq27
    | exact resolve eq27 eq66007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66056 : (k x y) = (τ (k x (σ y))) ∨ x = y := by
    first
    | exact superpose eq66007 eq59
    | exact resolve eq59 eq66007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq66007
  have eq66465 : (σ (k x y)) = (k x (σ y)) ∨ x = y := by
    first
    | exact superpose eq66056 eq15
    | exact resolve eq15 eq66056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66056
  have eq66530 : (k (σ x) (σ y)) = (k x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq66465
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq66465
    | exact resolve eq66465 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq66465
  have eq66550 : (σ (M.op x y)) = (k x (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq66530 eq52075
    | exact resolve eq52075 eq66530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52075 eq66530
  have eq66554 : (σ (M.op x y)) = (k x (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq66550
  have eq69338 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq66554 eq50181
    | exact resolve eq50181 eq66554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50181 eq66554
  have eq69340 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq69338
  have eq70937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq69340 eq66047
    | exact resolve eq66047 eq69340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66047 eq69340
  have eq70966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq70937
  have eq70970 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq70966
       have r₂ := eq28
       grind)
    | exact resolve eq70966 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70966
  have eq70974 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq70970 eq30
    | exact resolve eq30 eq70970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq70970
  have eq71162 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq70974
    | exact resolve eq70974 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq70974
  have eq71163 : x = y := by grind
  clear eq71162
  have eq71164 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq71163
       grind)
    | exact superpose eq71163 eq19
    | exact resolve eq19 eq71163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq71165 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq71163
       grind)
    | exact superpose eq71163 eq25
    | exact resolve eq25 eq71163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq71163
  have eq71306 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq71165
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq71165
    | exact resolve eq71165 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq71165
  have eq71308 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq71306 eq27
    | exact resolve eq27 eq71306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq71306
  have eq71482 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq71164
       have i₂ := eq335 X0 x
       grind)
    | (have i₁ := eq71164
       have i₂ := eq335 x X0
       grind)
    | exact superpose eq335 eq71164
    | exact resolve eq71164 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq71555 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq650 X0 x
       have i₂ := eq71164
       grind)
    | exact superpose eq71164 eq650
    | exact resolve eq650 eq71164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq71164
  have eq71893 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71308 eq4237
    | exact resolve eq4237 eq71308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4237
  have eq72015 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq71893
       have r₂ := eq28
       grind)
    | exact resolve eq71893 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71893
  have eq72112 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71308 eq71482
    | exact resolve eq71482 eq71308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71308
  have eq73152 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq72112 eq28
    | exact resolve eq28 eq72112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq73229 : (k (M.op x y) (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq72112 eq72015
    | exact resolve eq72015 eq72112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72015 eq72112
  have eq73235 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (τ (M.op x y))) := by
    first
    | exact superpose eq73229 eq124
    | exact resolve eq124 eq73229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq73265 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq73235
       have i₂ := eq15 sF0
       grind)
    | exact superpose eq15 eq73235
    | exact resolve eq73235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73235
  have eq73294 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 X0) ∨ (M.op X0 X0) = (σ (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq73265 eq5058
    | (have j0 := eq5058 X0 (M.op x y)
       grind)
    | exact resolve eq5058 eq73265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5058 eq73265
  have eq73298 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op X0 X0) = (σ (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq73294 X0
       have i₂ := eq71482 X0
       grind)
    | exact superpose eq71482 eq73294
    | (have j0 := eq73294 X0
       grind)
    | exact resolve eq73294 eq71482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73294
  have eq73309 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op X0 X0) = (σ (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq73298
    | (have j0 := eq73298 X0
       grind)
    | exact resolve eq73298 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq73298
  have eq73314 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq73309 X0
       grind)
    | (have r₁ := eq73309 X0
       have r₂ := eq73152
       grind)
    | exact resolve eq73309 eq73152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73309
  have eq73317 : (M.op x y) = (σ (σ (M.op x y))) := by
    first
    | (have i₁ := eq73314 x
       have i₂ := eq71482 x
       grind)
    | exact superpose eq71482 eq73314
    | exact resolve eq73314 eq71482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73314
  have eq73320 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq73317 eq16
    | exact resolve eq16 eq73317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73317
  have eq73727 : (M.op (M.op x y) (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq71555 eq73229
    | exact resolve eq73229 eq71555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71555 eq73229
  have eq73728 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq73320 eq73727
    | exact resolve eq73727 eq73320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73320 eq73727
  have eq73784 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq73728
       have i₂ := eq71482 sF0
       grind)
    | exact superpose eq71482 eq73728
    | exact resolve eq73728 eq71482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71482 eq73728
  have eq73823 : False := by grind
  exact eq73823

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_x_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  clear eq48
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
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq540 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq540 X2 X0
       grind)
    | exact superpose eq540 eq16
    | exact resolve eq16 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq540 X2 (M.op X1 (M.op X0 X0))
       grind)
    | (have i₁ := eq176 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq540 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq540 eq176
    | exact resolve eq176 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq571 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1
       have i₂ := eq540 X0 X1
       grind)
    | (have i₁ := eq181 X0
       have i₂ := eq540 X0 X1
       grind)
    | exact superpose eq540 eq181
    | exact resolve eq181 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (σ x) = (M.op (k (M.op (σ y) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq178 sF3
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq178
    | exact resolve eq178 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq181
  have eq1237 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq1239 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  clear eq26
  have eq1241 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1285 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1237
       grind)
    | exact superpose eq1237 eq41
    | exact resolve eq41 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1286 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1285
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1285
    | exact resolve eq1285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1285
  have eq1288 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1286
    | exact resolve eq1286 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1288 eq1239
    | exact resolve eq1239 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq1288
  have eq1305 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1298
       have r₂ := eq27
       grind)
    | exact resolve eq1298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1321 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1305 eq540
    | exact resolve eq540 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (σ y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq1305 eq541
    | exact resolve eq541 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1348 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (σ y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq1323 X0 X0
       have i₂ := eq571 X0 sF3
       grind)
    | exact superpose eq571 eq1323
    | exact resolve eq1323 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1357 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1321 eq1348
    | exact resolve eq1348 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1360 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1321 eq1357
    | exact resolve eq1357 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321 eq1357
  have eq1464 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1360 eq153
    | exact resolve eq153 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1360
  have eq1467 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1464
    | exact resolve eq1464 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1464
  have eq1470 : y = (M.op y y) := by
    first
    | (have j1 := eq1241 y
       grind)
    | (have r₁ := eq1467
       have r₂ := eq1241 y
       grind)
    | exact resolve eq1467 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1486 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq540 y X0
       have i₂ := eq1470
       grind)
    | exact superpose eq1470 eq540
    | exact resolve eq540 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq1488 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1 y
       have i₂ := eq1470
       grind)
    | exact superpose eq1470 eq541
    | exact resolve eq541 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1492 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X1 X0 y
       have i₂ := eq1470
       grind)
    | exact superpose eq1470 eq567
    | exact resolve eq567 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq1495 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq571 y x
       have i₂ := eq1470
       grind)
    | exact superpose eq1470 eq571
    | exact resolve eq571 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1510 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1488 X0 X1
       have i₂ := eq571 X1 y
       grind)
    | exact superpose eq571 eq1488
    | exact resolve eq1488 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1519 : ∀ X0 : G, (M.op X0 X0) = (k y y) := by
    intro X0
    first
    | (have i₁ := eq1510 X0 x
       have i₂ := eq1486 x
       grind)
    | exact superpose eq1486 eq1510
    | exact resolve eq1510 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1521 : y = (k y y) := by
    first
    | (have i₁ := eq1519 x
       have i₂ := eq1486 x
       grind)
    | exact superpose eq1486 eq1519
    | exact resolve eq1519 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq1630 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1521
       grind)
    | exact superpose eq1521 eq41
    | exact resolve eq41 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1633 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1630
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1630
    | exact resolve eq1630 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1630
  have eq1644 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1633 eq1241
    | (have j0 := eq1241 (σ y)
       grind)
    | (have r₁ := eq1241 (σ y)
       have r₂ := eq1633
       grind)
    | exact resolve eq1241 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1645 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1644
  have eq1646 : y = (σ y) := by
    first
    | (have i₁ := eq1645
       have i₂ := eq1486 sF3
       grind)
    | exact superpose eq1486 eq1645
    | exact resolve eq1645 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1650 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1646
       grind)
    | exact superpose eq1646 eq18
    | exact resolve eq18 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1759 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1495 X0
       have i₂ := eq1646
       grind)
    | exact superpose eq1646 eq1495
    | exact resolve eq1495 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1780 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1 y
       have i₂ := eq1495 y
       grind)
    | exact superpose eq1495 eq541
    | exact resolve eq541 eq1495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq1781 : ∀ X0 X1 : G, (M.op (M.op (k y y) X0) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X1 y X0
       have i₂ := eq1495 y
       grind)
    | exact superpose eq1495 eq565
    | exact resolve eq565 eq1495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq1495
  have eq1824 : ∀ X0 : G, (M.op (M.op (k y y) X0) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1781 X0 x
       have i₂ := eq1492 (M.op (k y y) X0) x
       grind)
    | exact superpose eq1492 eq1781
    | exact resolve eq1781 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492 eq1781
  have eq1825 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (k y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1780 X0 X1
       have i₂ := eq571 X1 (k y y)
       grind)
    | exact superpose eq571 eq1780
    | exact resolve eq1780 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq1780
  have eq1855 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ y)) X0) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1824 X0
       have i₂ := eq1646
       grind)
    | exact superpose eq1646 eq1824
    | exact resolve eq1824 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1856 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1825 X0 X1
       have i₂ := eq1521
       grind)
    | exact superpose eq1521 eq1825
    | exact resolve eq1825 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq1825
  have eq1876 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1633 eq1855
    | exact resolve eq1855 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq1877 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1856 X0 X1
       have i₂ := eq1646
       grind)
    | exact superpose eq1646 eq1856
    | exact resolve eq1856 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq1887 : ∀ X0 : G, (M.op (k (σ y) X0) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1759 eq1876
    | exact resolve eq1876 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1888 : ∀ X0 : G, (M.op X0 X0) = (k y (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1877 X0 x
       have i₂ := eq1486 x
       grind)
    | exact superpose eq1486 eq1877
    | exact resolve eq1877 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486 eq1877
  have eq1893 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1888 X0
       have i₂ := eq1646
       grind)
    | exact superpose eq1646 eq1888
    | exact resolve eq1888 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1895 : ∀ X0 : G, (σ y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq1633 eq1893
    | exact resolve eq1893 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq1954 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq575
       have i₂ := eq1895 sF3
       grind)
    | exact superpose eq1895 eq575
    | exact resolve eq575 eq1895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq1895
  have eq1955 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1633 eq1954
    | exact resolve eq1954 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633 eq1954
  have eq1988 : (σ x) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1759 eq1955
    | exact resolve eq1955 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759 eq1955
  have eq2050 : (τ (σ x)) = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1988 eq108
    | exact resolve eq108 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1988
  have eq2051 : (τ (σ x)) = (k (σ y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2050
       have i₂ := eq1646
       grind)
    | exact superpose eq1646 eq2050
    | exact resolve eq2050 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646 eq2050
  have eq2052 : x = (k (σ y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq30 eq2051
    | exact resolve eq2051 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2051
  have eq3004 : (τ (M.op (σ x) (σ y))) = (M.op x (σ y)) := by
    first
    | exact superpose eq2052 eq1887
    | exact resolve eq1887 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887 eq2052
  have eq3021 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1650 eq3004
    | exact resolve eq3004 eq1650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq3004
  have eq3040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3021 eq14
    | exact resolve eq14 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq3041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3040
    | exact resolve eq3040 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3040
  have eq3044 : False := by grind
  exact eq3044
