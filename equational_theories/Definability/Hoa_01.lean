import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation2683 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2683 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  clear eq18
  have eq68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq82 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  clear eq19
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq354 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83 x y
       grind)
    | exact superpose eq83 eq16
    | (have j1 := eq83 x y
       grind)
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1869 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1910 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1869 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1869
    | (have j0 := eq1869 X0 X1
       grind)
    | exact resolve eq1869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq2027 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq368 (τ X1) (τ X0)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq368
    | (have j0 := eq368 (τ X1) (τ X0)
       grind)
    | exact resolve eq368 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq2042 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2027 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2027
    | (have j0 := eq2027 X0 X1
       grind)
    | exact resolve eq2027 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2045 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2042 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2042
    | (have j0 := eq2042 X0 X1
       grind)
    | exact resolve eq2042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq2047 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2045 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2045
    | (have j0 := eq2045 X0 X1
       grind)
    | exact resolve eq2045 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq2048 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2047 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2047
    | (have j0 := eq2047 X0 X1
       grind)
    | exact resolve eq2047 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq2049 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2048 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2048
    | (have j0 := eq2048 X0 X1
       grind)
    | exact resolve eq2048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2050 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2049 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2049
    | (have j0 := eq2049 X0 X1
       grind)
    | exact resolve eq2049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049
  have eq2802 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq354
       have i₂ := eq1910 x y
       grind)
    | exact superpose eq1910 eq354
    | (have j1 := eq1910 (σ x) (σ y)
       grind)
    | (have r₁ := eq354
       have r₂ := eq1910 x y
       grind)
    | (have r₁ := eq354
       have r₂ := eq1910 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq354
       have r₂ := eq1910 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq354 eq1910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq1910
  have eq2803 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2802
  have eq30367 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2803
       grind)
    | exact superpose eq2803 eq16
    | exact resolve eq16 eq2803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803
  have eq30368 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30367
       have r₂ := eq22 x
       grind)
    | exact resolve eq30367 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30367
  have eq30636 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq30368
       grind)
    | exact superpose eq30368 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq30368
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq30368
       grind)
    | exact resolve eq13 eq30368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30368
  have eq30694 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq30636
  have eq40909 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30694
       grind)
    | exact superpose eq30694 eq16
    | exact resolve eq16 eq30694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30694
  have eq40910 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq40909
       have r₂ := eq22 x
       grind)
    | exact resolve eq40909 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40909
  have eq40920 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq368 x y
       have i₂ := eq40910
       grind)
    | exact superpose eq40910 eq368
    | (have j0 := eq368 x y
       grind)
    | exact resolve eq368 eq40910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq40910
  have eq40944 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq40920
  have eq40945 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq40944
  have eq41386 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40945
       grind)
    | exact superpose eq40945 eq16
    | exact resolve eq16 eq40945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41409 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq40945
       grind)
    | exact superpose eq40945 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq40945
       grind)
    | exact resolve eq13 eq40945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40945
  have eq41471 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq41409
  have eq41472 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq41471
  have eq41489 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq41472
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq41472
    | exact resolve eq41472 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41472
  have eq41723 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq41489
       grind)
    | exact superpose eq41489 eq10
    | exact resolve eq10 eq41489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41489
  have eq41863 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq41723
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41723
    | exact resolve eq41723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41723
  have eq41865 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41863
       grind)
    | exact superpose eq41863 eq16
    | exact resolve eq16 eq41863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41863
  have eq41866 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq41865
       have r₂ := eq22 x
       grind)
    | exact resolve eq41865 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41865
  have eq42071 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq41866
       grind)
    | exact superpose eq41866 eq10
    | exact resolve eq10 eq41866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41866
  have eq42212 : y = (k y x) := by
    first
    | (have i₁ := eq42071
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq42071
    | exact resolve eq42071 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42071
  have eq42227 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2050 y x
       have i₂ := eq42212
       grind)
    | exact superpose eq42212 eq2050
    | (have j0 := eq2050 y x
       grind)
    | (have r₁ := eq2050 y x
       have r₂ := eq42212
       grind)
    | exact resolve eq2050 eq42212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050 eq42212
  have eq42248 : x = y ∨ y = (M.op x y) := by grind
  clear eq42227
  have eq42567 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42248
       grind)
    | exact superpose eq42248 eq16
    | exact resolve eq16 eq42248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42248
  have eq42572 : y = (M.op x y) := by
    first
    | (have r₁ := eq42567
       have r₂ := eq22 x
       grind)
    | exact resolve eq42567 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42567
  have eq42577 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41386
       have i₂ := eq42572
       grind)
    | exact superpose eq42572 eq41386
    | exact resolve eq41386 eq42572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41386 eq42572
  have eq42643 : (σ x) = (σ y) := by grind
  clear eq42577
  have eq42957 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq42643
       grind)
    | exact superpose eq42643 eq10
    | exact resolve eq10 eq42643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42643
  have eq43097 : x = y := by
    first
    | (have i₁ := eq42957
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42957
    | exact resolve eq42957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42957
  have eq43101 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43097
       grind)
    | exact superpose eq43097 eq16
    | exact resolve eq16 eq43097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43097
  have eq43107 : False := by grind
  exact eq43107

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_y_pyy_pxy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
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
  have eq47 : (σ (k x (k x x))) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq36
    | exact resolve eq36 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq44
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq98 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k X1 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq107 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq108 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq112 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq108
    | exact resolve eq108 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq114 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq112
    | exact resolve eq112 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq107
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq123 : (M.op x x) = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq122
    | exact resolve eq122 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq139
    | exact resolve eq139 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq142
    | exact resolve eq142 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq151 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (σ (k (M.op x y) (M.op (M.op x y) (M.op x y)))) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq144 eq38
    | exact resolve eq38 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq241 : x = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (M.op X1 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 X0)) = (M.op (M.op (M.op (M.op x y) (M.op X0 y)) (M.op X2 X1)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X1 (M.op X4 (M.op (M.op X0 X3) (M.op X2 X3)))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3)) X4
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X4 X2)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53 X0 x X2 X4
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4) (M.op X3 X4)) = (M.op X0 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4 X3 X2
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) X2 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 x X2
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) (M.op X0 X4)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X3 (M.op X2 X4) (M.op X0 X4)
       have i₂ := eq53 X0 X4 X2 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X4 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X2 X3) X4
       have i₂ := eq53 X0 X3 X2 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op x y)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 (M.op y X2))
       have i₂ := eq53 X0 X1 X2 y
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x X1) (M.op (M.op X1 X2) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) (M.op (M.op X2 X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op X2 X1) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x X1) (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) X1) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq534 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) (M.op (σ x) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) (M.op X0 (M.op X5 X2))) (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X4 X5))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 (M.op X0 (M.op X5 X2)) X3 X4 X5
       have i₂ := eq53 X0 X1 X2 X5
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) X2) (M.op (M.op X2 X1) (σ x))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X0 (M.op X4 X2))) X5) (M.op (M.op X5 X4) (M.op (M.op X0 X1) (M.op X2 X1)))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X5 X3 (M.op X0 (M.op X4 X2)) X4
       have i₂ := eq53 X0 X1 X2 X4
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X0 X4)) X5) (M.op (M.op X5 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X5 X3 (M.op X0 X4) (M.op X2 X4)
       have i₂ := eq53 X0 X4 X2 X1
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 X3 X2 x
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq56 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op (M.op X1 X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X2) X3 (M.op X1 X4) (M.op X2 X4)
       have i₂ := eq56 X2 X0 X1 X4
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X2) (M.op (M.op (M.op X3 X4) (M.op X5 X4)) X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 X5) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X1 X2 (M.op (M.op X3 X4) (M.op X5 X4)) (M.op (M.op X0 X5) X3)
       have i₂ := eq56 X3 X0 X5 X4
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq1212 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1213 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1212 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1299 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq241 eq463
    | exact resolve eq463 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq250 eq463
    | exact resolve eq463 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1310 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 y) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq463
    | exact resolve eq463 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1311 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq52 eq463
    | exact resolve eq463 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1313 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463 (M.op X0 X1) (M.op X2 X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq463
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1318 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq463 (M.op X0 X1) X2 (M.op X1 X2)
       have i₂ := eq463 X0 X1 X2
       grind)
    | exact superpose eq463 eq463
    | exact resolve eq463 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1372 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X3 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3
       have i₂ := eq463 X0 X1 X2
       grind)
    | exact superpose eq463 eq14
    | exact resolve eq14 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1448 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (σ y))) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq464
    | exact resolve eq464 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1466 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 (M.op y sF0))
       have i₂ := eq464 X0 y sF0
       grind)
    | exact superpose eq464 eq54
    | exact resolve eq54 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1694 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq568
    | exact resolve eq568 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1697 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X2)) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq568 X1 (M.op (M.op X0 (M.op X2 X3)) X2) X3
       have i₂ := eq464 X0 X2 X3
       grind)
    | exact superpose eq464 eq568
    | exact resolve eq568 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1702 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq568 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq463 X0 X2 X3
       grind)
    | exact superpose eq463 eq568
    | exact resolve eq568 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1707 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq461 eq568
    | exact resolve eq568 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq1712 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | exact superpose eq241 eq568
    | exact resolve eq568 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq1717 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq250 eq568
    | exact resolve eq568 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1729 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq568 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq464 X0 X2 X2
       grind)
    | exact superpose eq464 eq568
    | exact resolve eq568 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1734 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq568 (M.op (M.op X0 (M.op X1 X2)) X2) X1 X2
       have i₂ := eq463 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq463 eq568
    | exact resolve eq568 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1786 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op x sF3)
       have i₂ := eq568 sF4 x sF3
       grind)
    | exact superpose eq568 eq52
    | exact resolve eq52 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1894 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1213 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq1213
    | exact resolve eq1213 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1902 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1894 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1894
    | exact resolve eq1894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq1907 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1902 X0
       have i₂ := eq1213 X0
       grind)
    | exact superpose eq1213 eq1902
    | exact resolve eq1902 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq2739 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1786 eq464
    | exact resolve eq464 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq11641 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X2) (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq521 X1 X2 (σ X0) (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq521
    | exact resolve eq521 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11900 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq530 eq521
    | exact resolve eq521 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq11925 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op X3 X1) X4))) X2) = (M.op (M.op X0 X1) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq441 X0 X2 (M.op (M.op X3 X1) X4) (M.op X3 X4)
       have i₂ := eq521 X0 X1 X3 X4
       grind)
    | exact superpose eq521 eq441
    | exact resolve eq441 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq12098 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0 X1
    first
    | exact superpose eq2739 eq11900
    | exact resolve eq11900 eq2739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739 eq11900
  have eq12181 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11641 X0 X1 X2
       have i₂ := eq1313 (σ (M.op X0 X0)) X2 (σ X0)
       grind)
    | exact superpose eq1313 eq11641
    | exact resolve eq11641 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313 eq11641
  have eq13160 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1310 (M.op (M.op y (M.op X0 X0)) X0)
       have i₂ := eq562 y X0 X0 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq562 eq1310
    | exact resolve eq1310 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq13161 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1311 (M.op (M.op sF3 (M.op x x)) x)
       have i₂ := eq562 sF3 x x (M.op sF3 (M.op x x))
       grind)
    | exact superpose eq562 eq1311
    | exact resolve eq1311 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq1311
  have eq13512 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq13161 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq13161
    | exact resolve eq13161 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13161
  have eq17715 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1729 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X2
       have i₂ := eq463 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq463 eq1729
    | exact resolve eq1729 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18278 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1734 (M.op (M.op X0 X2) X1) X2 X1
       have i₂ := eq463 X0 X2 X1
       grind)
    | exact superpose eq463 eq1734
    | exact resolve eq1734 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18295 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq1304 eq1734
    | exact resolve eq1734 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18743 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq435
    | (have j0 := eq435 X0 (σ x) X1
       grind)
    | exact resolve eq435 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq19010 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18743 X1 X0
       have i₂ := eq1729 X0 X1 sF4
       grind)
    | exact superpose eq1729 eq18743
    | exact resolve eq18743 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729 eq18743
  have eq26392 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x X1))) = (M.op (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) y) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq528 eq477
    | exact resolve eq477 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq528
  have eq26515 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op y (M.op x X1))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq26392
    | exact resolve eq26392 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq26392
  have eq30073 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 y)) = (M.op (M.op x (σ X0)) (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq505 X1 (σ X0) (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq505
    | exact resolve eq505 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq37012 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))))) (M.op (σ x) (M.op X2 (M.op (σ x) (M.op (σ y) X0))))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq256 eq534
    | exact resolve eq534 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq37338 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) = (M.op (M.op X0 (σ x)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq534 eq464
    | exact resolve eq464 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq37565 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (σ y))) (M.op (σ x) (M.op X2 (M.op (σ x) (M.op (σ y) X0))))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq12098 eq37012
    | exact resolve eq37012 eq12098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12098 eq37012
  have eq38033 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op (M.op (M.op x y) (σ x)) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq428 X0 y X0
       have i₂ := eq19010 sF0 (M.op X0 y)
       grind)
    | exact superpose eq19010 eq428
    | exact resolve eq428 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq43031 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq549 eq568
    | exact resolve eq568 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq43133 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq27 eq43031
    | (have j0 := eq43031 X0 X1
       grind)
    | exact resolve eq43031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43031
  have eq43320 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ x))) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1717 eq43133
    | exact resolve eq43133 eq1717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717 eq43133
  have eq47908 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq437 X3 X0 X2 X1 (M.op X3 (M.op X2 X1))
       have i₂ := eq521 X0 X1 X3 (M.op X2 X1)
       grind)
    | exact superpose eq521 eq437
    | exact resolve eq437 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq521
  have eq52532 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) (M.op (M.op X1 X3) X2)) X4) = (M.op (M.op (M.op X0 X1) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq464 (M.op (M.op (M.op X0 X2) (M.op (M.op X1 X3) X2)) X4) X3 X4
       have i₂ := eq459 X0 X2 X1 X3 X4
       grind)
    | exact superpose eq459 eq464
    | exact resolve eq464 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64066 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq524 X2 (M.op X0 X1) X1 x x
       have i₂ := eq459 X1 x X0 X1 x
       grind)
    | exact superpose eq459 eq524
    | exact resolve eq524 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq524
  have eq68872 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq569 X0 X2 (M.op X1 X2) X1 X3
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq569
    | exact resolve eq569 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69550 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq464 (M.op (M.op (M.op X0 X3) X1) X4) (M.op X3 X2) X4
       have i₂ := eq569 X0 X3 X1 X4 X2
       grind)
    | exact superpose eq569 eq464
    | exact resolve eq464 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq107317 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1))) (M.op X2 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq535 X2 X3 X1 X0 X1 X3
       have i₂ := eq568 (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1))) (M.op X2 X3) (M.op X1 X3)
       grind)
    | exact superpose eq568 eq535
    | exact resolve eq535 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107327 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) (M.op X3 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq469 (M.op X2 X2) (M.op X1 X3) X2 (M.op X0 X1) (M.op X3 (M.op X1 X3))
       have i₂ := eq535 X2 X2 (M.op X1 X3) X0 X1 X3
       grind)
    | exact superpose eq535 eq469
    | exact resolve eq469 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq535
  have eq107623 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107327 X0 X1 X2 x
       have i₂ := eq1318 (M.op X2 X2) X1 x
       grind)
    | exact superpose eq1318 eq107327
    | exact resolve eq107327 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107327
  have eq119838 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq470 X0 X2 (M.op X2 X1) (M.op X1 X1) (M.op X2 X2)
       have i₂ := eq550 X2 X1 X1 X0 X2 X2
       grind)
    | exact superpose eq550 eq470
    | exact resolve eq470 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq126154 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X0 X4)) X5) (M.op (M.op X5 (M.op X2 X4)) (M.op X1 (M.op X0 (M.op X1 X2))))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq553 X0 X1 X2 X3 X4 X5
       have i₂ := eq64066 (M.op X0 (M.op X1 X2)) X1 (M.op X5 (M.op X2 X4))
       grind)
    | (have i₁ := eq553 X0 X1 X2 X3 X4 X5
       have i₂ := eq64066 X1 (M.op X0 (M.op X1 X2)) (M.op X5 (M.op X2 X4))
       grind)
    | exact superpose eq64066 eq553
    | exact resolve eq553 eq64066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq146029 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X4) X4) = (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq568 (M.op X0 X4) X4 X2
       have i₂ := eq577 X4 X0 X1 X2 X3 X2
       grind)
    | exact superpose eq577 eq568
    | exact resolve eq568 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq577
  have eq146406 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X4) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq146029 X0 X4 x x X1
       have i₂ := eq107623 (M.op X0 X4) X4 (M.op x x)
       grind)
    | exact superpose eq107623 eq146029
    | exact resolve eq146029 eq107623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107623 eq146029
  have eq158313 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) = (M.op X0 (M.op X1 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq470 X0 X1 X2 (M.op X1 (M.op X2 X3)) (M.op X1 (M.op X3 X2))
       have i₂ := eq126154 X1 X2 X3 X0 X2 X1
       grind)
    | exact superpose eq126154 eq470
    | exact resolve eq470 eq126154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq126154
  have eq256936 : (σ (k x (k x x))) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq47
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq47
    | exact resolve eq47 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq256937 : (σ (k x (k x x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq256936
       have i₂ := eq1213 sF2
       grind)
    | exact superpose eq1213 eq256936
    | exact resolve eq256936 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256936
  have eq256938 : (σ (k x (M.op x x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq256937
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq256937
    | exact resolve eq256937 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq256937
  have eq256939 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq256938
       have i₂ := eq1213 x
       grind)
    | exact superpose eq1213 eq256938
    | exact resolve eq256938 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256938
  have eq265377 : (σ (k (M.op x y) (M.op (M.op x y) (M.op x y)))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq188
       have i₂ := eq1213 sF1
       grind)
    | exact superpose eq1213 eq188
    | exact resolve eq188 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq265378 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq265377
       have i₂ := eq1213 sF0
       grind)
    | exact superpose eq1213 eq265377
    | exact resolve eq265377 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq265377
  have eq265379 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op x y) (M.op x x))) := by
    first
    | exact superpose eq1712 eq265378
    | exact resolve eq265378 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712 eq265378
  have eq273442 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (σ (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1734 X0 (σ (M.op X2 X2)) X1
       have i₂ := eq12181 X2 X0 X1
       grind)
    | exact superpose eq12181 eq1734
    | exact resolve eq1734 eq12181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq12181
  have eq277279 : (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (M.op (σ x) (σ x)))) = (σ (M.op (M.op x (M.op x x)) (M.op x (M.op x x)))) := by
    first
    | (have i₁ := eq74 (M.op x (M.op x x))
       have i₂ := eq256939
       grind)
    | exact superpose eq256939 eq74
    | exact resolve eq74 eq256939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq256939
  have eq277350 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq277279
       have i₂ := eq1299 (M.op x x)
       grind)
    | exact superpose eq1299 eq277279
    | exact resolve eq277279 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299 eq277279
  have eq277379 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1304 eq277350
    | exact resolve eq277350 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq277350
  have eq277407 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq144 eq277379
    | exact resolve eq277379 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq277379
  have eq277430 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq277407 eq250
    | exact resolve eq250 eq277407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq277439 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq277407 eq18295
    | exact resolve eq18295 eq277407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18295 eq277407
  have eq278052 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq277430 eq463
    | exact resolve eq463 eq277430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq277430
  have eq278867 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op x y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq265379
       have i₂ := eq119838 sF0 x x
       grind)
    | (have i₁ := eq265379
       have i₂ := eq119838 sF0 x x
       grind)
    | exact superpose eq119838 eq265379
    | exact resolve eq265379 eq119838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265379
  have eq313336 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1448 X0 X1
       have i₂ := eq64066 (M.op X0 X1) sF3 sF4
       grind)
    | (have i₁ := eq1448 X0 X1
       have i₂ := eq64066 sF3 (M.op X0 X1) sF4
       grind)
    | exact superpose eq64066 eq1448
    | exact resolve eq1448 eq64066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq547660 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq313336 eq464
    | exact resolve eq464 eq313336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq313336
  have eq588223 : ∀ X0 : G, (M.op (σ x) (σ (M.op x y))) = (M.op (M.op (M.op (σ (M.op x y)) X0) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq277439 sF1
       have i₂ := eq146406 sF1 sF1 x
       grind)
    | (have i₁ := eq277439 sF1
       have i₂ := eq146406 sF1 x sF1
       grind)
    | exact superpose eq146406 eq277439
    | exact resolve eq277439 eq146406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146406 eq277439
  have eq674693 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op X3 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1372 X0 X1 X2 X3
       have i₂ := eq18278 X0 (M.op X3 (M.op X1 X2)) X3
       grind)
    | (have i₁ := eq1372 X0 X1 X2 X3
       have i₂ := eq18278 X0 X3 (M.op X3 (M.op X1 X2))
       grind)
    | exact superpose eq18278 eq1372
    | exact resolve eq1372 eq18278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq698678 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X3)) = (M.op X1 (M.op X2 (M.op X0 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1697 X0 X1 X2 X3
       have i₂ := eq64066 (M.op X0 (M.op X2 X3)) X2 X1
       grind)
    | (have i₁ := eq1697 X0 X1 X2 X3
       have i₂ := eq64066 X2 (M.op X0 (M.op X2 X3)) X1
       grind)
    | exact superpose eq64066 eq1697
    | exact resolve eq1697 eq64066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq1117704 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op X2 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68872 X0 X1 X2 X3
       have i₂ := eq1702 X2 X0 X3 X1
       grind)
    | exact superpose eq1702 eq68872
    | exact resolve eq68872 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68872
  have eq1117705 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) = (M.op X0 (M.op X2 (M.op X3 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1117704 X0 X1 X2 X3
       have i₂ := eq1702 X1 X0 X2 X3
       grind)
    | exact superpose eq1702 eq1117704
    | exact resolve eq1117704 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117704
  have eq1194515 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (M.op X2 (M.op X3 X1))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq107317 X0 X1 X2 X3
       have i₂ := eq18278 (M.op X0 X1) (M.op X2 (M.op X3 X1)) (M.op X2 X3)
       grind)
    | (have i₁ := eq107317 X0 X1 X2 X3
       have i₂ := eq18278 (M.op X0 X1) (M.op X2 X3) (M.op X2 (M.op X3 X1))
       grind)
    | exact superpose eq18278 eq107317
    | exact resolve eq107317 eq18278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107317
  have eq1634499 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x x) (M.op X0 X1)) (M.op X0 (M.op X1 x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1194515 y x X0 X1
       have i₂ := eq123
       grind)
    | exact superpose eq123 eq1194515
    | exact resolve eq1194515 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1634505 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1634499 x x
       have i₂ := eq1194515 x x x x
       grind)
    | exact superpose eq1194515 eq1634499
    | exact resolve eq1634499 eq1194515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194515 eq1634499
  have eq1896260 : (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) = (σ (M.op (M.op (M.op (M.op x y) (σ x)) (σ x)) (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) := by
    first
    | exact superpose eq38033 eq1907
    | exact resolve eq1907 eq38033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq1898244 : (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) = (σ (M.op x (M.op y (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x))))))) := by
    first
    | exact superpose eq38033 eq1896260
    | exact resolve eq1896260 eq38033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38033 eq1896260
  have eq1899460 : (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) = (σ (M.op x (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) := by
    first
    | (have i₁ := eq1898244
       have i₂ := eq26515 x (M.op y (M.op (M.op sF0 sF2) sF2))
       grind)
    | exact superpose eq26515 eq1898244
    | exact resolve eq1898244 eq26515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26515 eq1898244
  have eq1900439 : (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) = (σ (M.op x (M.op y (M.op (M.op (M.op (M.op x y) (σ x)) (σ x)) (M.op x y))))) := by
    first
    | (have i₁ := eq1899460
       have i₂ := eq1117705 x sF0 y (M.op (M.op sF0 sF2) sF2)
       grind)
    | (have i₁ := eq1899460
       have i₂ := eq1117705 x (M.op (M.op sF0 sF2) sF2) sF0 y
       grind)
    | exact superpose eq1117705 eq1899460
    | exact resolve eq1899460 eq1117705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117705 eq1899460
  have eq1901165 : (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) = (σ (M.op x (M.op y (M.op (M.op x y) (M.op (M.op (M.op x y) (σ x)) (σ x)))))) := by
    first
    | (have i₁ := eq1900439
       have i₂ := eq158313 x y (M.op (M.op sF0 sF2) sF2) sF0
       grind)
    | (have i₁ := eq1900439
       have i₂ := eq158313 x y sF0 (M.op (M.op sF0 sF2) sF2)
       grind)
    | exact superpose eq158313 eq1900439
    | exact resolve eq1900439 eq158313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900439
  have eq1901654 : (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) = (σ (M.op x (M.op y (M.op (M.op x y) (M.op (σ x) (M.op (M.op x y) (σ x))))))) := by
    first
    | (have i₁ := eq1901165
       have i₂ := eq158313 y sF0 (M.op sF0 sF2) sF2
       grind)
    | (have i₁ := eq1901165
       have i₂ := eq158313 y sF0 sF2 (M.op sF0 sF2)
       grind)
    | exact superpose eq158313 eq1901165
    | exact resolve eq1901165 eq158313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901165
  have eq1902014 : (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) = (σ (M.op x (M.op y (M.op (σ x) (σ x))))) := by
    first
    | (have i₁ := eq1901654
       have i₂ := eq698678 sF2 y sF0 sF2
       grind)
    | exact superpose eq698678 eq1901654
    | exact resolve eq1901654 eq698678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698678 eq1901654
  have eq1902251 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (M.op (M.op x y) (σ x)) (σ x)))))) := by
    first
    | (have i₁ := eq1902014
       have i₂ := eq13160 sF2
       grind)
    | exact superpose eq13160 eq1902014
    | exact resolve eq1902014 eq13160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13160 eq1902014
  have eq1902404 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op (σ x) (M.op (M.op x y) (σ x))))))) := by
    first
    | (have i₁ := eq1902251
       have i₂ := eq158313 x y (M.op sF0 sF2) sF2
       grind)
    | (have i₁ := eq1902251
       have i₂ := eq158313 x y sF2 (M.op sF0 sF2)
       grind)
    | exact superpose eq158313 eq1902251
    | exact resolve eq1902251 eq158313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158313 eq1902251
  have eq1902514 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x (M.op y (M.op x y))))) := by
    first
    | (have i₁ := eq1902404
       have i₂ := eq1318 y sF0 sF2
       grind)
    | exact superpose eq1318 eq1902404
    | exact resolve eq1902404 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq1902404
  have eq1902589 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (σ (M.op x x))) := by
    first
    | exact superpose eq1466 eq1902514
    | exact resolve eq1902514 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq1902514
  have eq1902634 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1902589
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq1902589
    | exact resolve eq1902589 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1902589
  have eq1902671 : (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) (σ x)) (σ x))) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq21 eq1902634
    | exact resolve eq1902634 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902634
  have eq1903380 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) X0) X0)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1902671
       have i₂ := eq19010 sF0 sF2
       grind)
    | exact superpose eq19010 eq1902671
    | exact resolve eq1902671 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010 eq1902671
  have eq1905331 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) X0) X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1903380 X0
       have i₂ := eq119838 (σ (M.op (M.op sF0 X0) X0)) sF2 x
       grind)
    | (have i₁ := eq1903380 X0
       have i₂ := eq119838 (σ (M.op (M.op sF0 X0) X0)) X1 sF2
       grind)
    | exact superpose eq119838 eq1903380
    | exact resolve eq1903380 eq119838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119838
  have eq1905338 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) X1) X1) = (σ (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0 X1
    first
    | exact superpose eq1903380 eq43320
    | exact resolve eq43320 eq1903380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43320 eq1903380
  have eq1920801 : ∀ X0 : G, (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op (M.op (M.op x y) X0) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1905338 eq588223
    | exact resolve eq588223 eq1905338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588223 eq1905338
  have eq2329057 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ x) X2)) = (M.op (M.op X0 (σ x)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1694 eq37338
    | exact resolve eq37338 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694 eq37338
  have eq4689251 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X4)) = (M.op (M.op X0 X2) (M.op X2 (M.op (M.op X3 X1) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq11925 X0 X1 X2 X3 X4
       have i₂ := eq18278 X0 (M.op X2 (M.op (M.op X3 X1) X4)) X2
       grind)
    | (have i₁ := eq11925 X0 X1 X2 X3 X4
       have i₂ := eq18278 X0 X2 (M.op X2 (M.op (M.op X3 X1) X4))
       grind)
    | exact superpose eq18278 eq11925
    | exact resolve eq11925 eq18278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11925
  have eq4689252 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X4)) = (M.op (M.op X0 (M.op X3 X1)) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq4689251 X0 X1 x X3 X4
       have i₂ := eq674693 X0 (M.op X3 X1) X4 x
       grind)
    | exact superpose eq674693 eq4689251
    | exact resolve eq4689251 eq674693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674693 eq4689251
  have eq5088794 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ x)) (M.op (M.op X0 (σ y)) (M.op X2 (M.op (σ x) (M.op (σ y) X0))))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq2329057 eq37565
    | exact resolve eq37565 eq2329057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37565 eq2329057
  have eq5088795 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ x)) (M.op X0 (M.op (σ y) (M.op X2 (M.op (σ x) (M.op (σ y) X0)))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5088794 X0 X1 X2
       have i₂ := eq1702 X0 (M.op (M.op X1 X2) sF2) sF3 (M.op X2 (M.op sF2 (M.op sF3 X0)))
       grind)
    | exact superpose eq1702 eq5088794
    | exact resolve eq5088794 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088794
  have eq5088796 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ x)) (M.op X0 (M.op (σ y) (M.op X2 (M.op (M.op (σ x) (σ y)) X0))))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq1707 eq5088795
    | exact resolve eq5088795 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq5088795
  have eq5198766 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X3) X4) = (M.op (M.op (M.op X0 X2) X2) (M.op (M.op X1 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52532 X0 X1 X2 X3 X4
       have i₂ := eq4689252 (M.op X0 X2) X2 (M.op X1 X3) X4
       grind)
    | exact superpose eq4689252 eq52532
    | exact resolve eq52532 eq4689252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52532
  have eq5198767 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X3) X4) = (M.op (M.op (M.op X0 X2) X2) (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5198766 X0 X1 X2 X3 X4
       have i₂ := eq1702 X1 (M.op (M.op X0 X2) X2) X3 X4
       grind)
    | exact superpose eq1702 eq5198766
    | exact resolve eq5198766 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702 eq5198766
  have eq5422312 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) (M.op X3 X4)) = (M.op (M.op (M.op X0 X3) X1) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69550 X0 X1 X2 X3 X4
       have i₂ := eq4689252 (M.op X0 (M.op X1 X2)) X2 X3 X4
       grind)
    | exact superpose eq4689252 eq69550
    | exact resolve eq69550 eq4689252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69550
  have eq5422313 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 X2) (M.op X1 X2)) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5422312 X0 X1 X2 X3 X4
       have i₂ := eq18278 X0 (M.op X1 X2) X2
       grind)
    | (have i₁ := eq5422312 X0 X1 X2 X3 X4
       have i₂ := eq18278 X0 X2 (M.op X1 X2)
       grind)
    | exact superpose eq18278 eq5422312
    | exact resolve eq5422312 eq18278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18278 eq5422312
  have eq5422314 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 X2) X2) (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5422313 X0 X1 X2 X3 X4
       have i₂ := eq4689252 (M.op X0 X2) X2 X1 (M.op X3 X4)
       grind)
    | exact superpose eq4689252 eq5422313
    | exact resolve eq5422313 eq4689252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689252 eq5422313
  have eq5946009 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X1) X3) X4) = (M.op (M.op (M.op X0 X3) X1) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq5422314 X0 X3 x X1 X4
       have i₂ := eq5198767 X0 X3 x X1 X4
       grind)
    | exact superpose eq5198767 eq5422314
    | exact resolve eq5422314 eq5198767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5198767 eq5422314
  have eq6603818 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 y)) = (M.op (M.op x X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30073 X0 X1
       have i₂ := eq47908 x (σ X0) X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq47908 eq30073
    | exact resolve eq30073 eq47908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30073 eq47908
  have eq6750458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1634505 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1634505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634505
  have eq6750475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq6750458
    | exact resolve eq6750458 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6750458
  have eq6750490 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq6750475
       have r₂ := eq28
       grind)
    | exact resolve eq6750475 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6750475
  have eq6751094 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6750490 eq5088796
    | exact resolve eq5088796 eq6750490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6750490
  have eq6751212 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f6751212_14 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = x := by
      intro X0
      grind
    have f6751212_15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ x)) (M.op X0 (M.op (σ y) (M.op X2 (M.op (M.op (σ x) (σ y)) X0))))) = X1 := by
      intro X0 X1 X2
      grind
    have f6751212_23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
    have f6751212_24 : (σ y) ≠ (σ x) := by grind
    have f6751212_25 : x ≠ (M.op y y) := by grind
    have f6751212_26 : y ≠ x := by grind
    have f6751212_28 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) ∨ x = (M.op y y) ∨ y = x := by
      intro X0
      first
      | (have j0 := f6751212_14 X0
         grind)
      | (have r₁ := f6751212_14 X0
         have r₂ := f6751212_23
         grind)
      | exact resolve f6751212_14 f6751212_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6751212_29 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) ∨ y = x := by
      intro X0
      first
      | (have j0 := f6751212_28 X0
         grind)
      | (have r₁ := f6751212_28 X0
         have r₂ := f6751212_25
         grind)
      | exact resolve f6751212_28 f6751212_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6751212_30 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) := by
      intro X0
      first
      | (have j0 := f6751212_29 X0
         grind)
      | (have r₁ := f6751212_29 X0
         have r₂ := f6751212_26
         grind)
      | exact resolve f6751212_29 f6751212_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6751212_31 : (σ y) = (σ x) := by
      first
      | (have i₁ := f6751212_30 x
         have i₂ := f6751212_15 x (σ x) (σ x)
         grind)
      | exact superpose f6751212_15 f6751212_30
      | exact resolve f6751212_30 f6751212_15
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f6751212_32 : False := by
      first
      | (have r₁ := f6751212_31
         have r₂ := f6751212_24
         grind)
      | exact resolve f6751212_31 f6751212_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f6751212_32
  clear eq5088796 eq6751094
  have eq6753696 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq6751212 eq151
    | exact resolve eq151 eq6751212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq6751212
  have eq6755118 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq6753696
    | exact resolve eq6753696 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753696
  have eq6755119 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6755118
  have eq6756479 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq114
       have i₂ := eq6755119
       grind)
    | exact superpose eq6755119 eq114
    | exact resolve eq114 eq6755119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq6757074 : ∀ X0 : G, y = (M.op (M.op x y) (σ (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq273442 y y X0
       have i₂ := eq6755119
       grind)
    | exact superpose eq6755119 eq273442
    | exact resolve eq273442 eq6755119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273442 eq6755119
  have eq6757428 : y = (M.op (M.op x y) (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6757074 x
       have i₂ := eq6603818 x y
       grind)
    | exact superpose eq6603818 eq6757074
    | exact resolve eq6757074 eq6603818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6603818 eq6757074
  have eq6757907 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6756479
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6756479
    | exact resolve eq6756479 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6756479
  have eq6784601 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op (M.op x y) X0) X0)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6757907 eq1905331
    | exact resolve eq1905331 eq6757907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905331 eq6757907
  have eq6785555 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1920801 eq6784601
    | exact resolve eq6784601 eq1920801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920801 eq6784601
  have eq6907504 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6757428 eq278867
    | exact resolve eq278867 eq6757428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278867 eq6757428
  have eq6908905 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6907504
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6907504
    | exact resolve eq6907504 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6907504
  have eq7738105 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6908905 eq547660
    | exact resolve eq547660 eq6908905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547660 eq6908905
  have eq7738565 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7738105
       have i₂ := eq5946009 (M.op sF2 sF1) (M.op sF1 sF1) sF3 sF3
       grind)
    | (have i₁ := eq7738105
       have i₂ := eq5946009 (M.op sF2 sF1) sF3 (M.op sF1 sF1) sF3
       grind)
    | exact superpose eq5946009 eq7738105
    | exact resolve eq7738105 eq5946009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5946009 eq7738105
  have eq7739151 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7738565
       have i₂ := eq17715 (M.op sF2 sF1) sF3 sF1
       grind)
    | exact superpose eq17715 eq7738565
    | exact resolve eq7738565 eq17715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17715 eq7738565
  have eq7740979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7739151 eq6785555
    | exact resolve eq6785555 eq7739151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6785555 eq7739151
  have eq7741599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7740979
  have eq7742140 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq7741599
       have r₂ := eq28
       grind)
    | exact resolve eq7741599 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7741599
  have eq7743611 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq7742140 eq30
    | exact resolve eq30 eq7742140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7742140
  have eq7744413 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq7743611
    | exact resolve eq7743611 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7743611
  have eq7744414 : x = y := by grind
  clear eq7744413
  have eq7744895 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq7744414
       grind)
    | exact superpose eq7744414 eq19
    | exact resolve eq19 eq7744414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq7744896 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq7744414
       grind)
    | exact superpose eq7744414 eq25
    | exact resolve eq25 eq7744414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq7744414
  have eq7745789 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq7744896
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq7744896
    | exact resolve eq7744896 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq7744896
  have eq7747951 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq13512 x
       have i₂ := eq7744895
       grind)
    | exact superpose eq7744895 eq13512
    | exact resolve eq13512 eq7744895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13512 eq7744895
  have eq7749128 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq7747951
    | exact resolve eq7747951 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq7747951
  have eq7749753 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq7749128
       have i₂ := eq64066 sF3 sF1 sF2
       grind)
    | (have i₁ := eq7749128
       have i₂ := eq64066 sF1 sF3 sF2
       grind)
    | exact superpose eq64066 eq7749128
    | exact resolve eq7749128 eq64066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64066 eq7749128
  have eq7750191 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq7745789 eq7749753
    | exact resolve eq7749753 eq7745789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7745789 eq7749753
  have eq7750480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq278052 eq7750191
    | exact resolve eq7750191 eq278052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278052 eq7750191
  have eq7750667 : False := by grind
  exact eq7750667

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pyx_x_pyx_Equation2702 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
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
  clear eq22
  have eq177 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op x y) = (k y x) ∨ x = (M.op y x) := by
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
  have eq189 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
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
  clear eq28
  have eq208 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq188
       grind)
    | exact superpose eq188 eq40
    | exact resolve eq40 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq480 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq479
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq479
    | exact resolve eq479 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq482 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq480
    | exact resolve eq480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq482 eq189
    | exact resolve eq189 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq571
       have r₂ := eq27
       grind)
    | exact resolve eq571 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq585 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq578 eq177
    | exact resolve eq177 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq578 eq585
    | exact resolve eq585 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq585
  have eq592 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq590
    | exact resolve eq590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq596 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq592
       grind)
    | exact superpose eq592 eq177
    | exact resolve eq177 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq592 eq596
    | exact resolve eq596 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq596
  have eq603 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq601
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq601
    | exact resolve eq601 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq605 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq603 eq179
    | exact resolve eq179 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq606 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq603 eq209
    | exact resolve eq209 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq608 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq603 eq27
    | exact resolve eq27 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq606
    | exact resolve eq606 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq611 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq603 eq609
    | exact resolve eq609 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq609
  have eq619 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq611 eq16
    | exact resolve eq16 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq634 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq619 eq177
    | exact resolve eq177 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq619 eq881
    | exact resolve eq881 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq1225 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq605 sF2
       have i₂ := eq634 sF2
       grind)
    | exact superpose eq634 eq605
    | exact resolve eq605 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq1792 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) ≠ (M.op (M.op X0 (σ y)) (σ x)) ∨ (M.op (M.op X0 (σ y)) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq889 eq12
    | (have j0 := eq12 (σ y) (M.op (M.op X0 (σ y)) (σ x))
       grind)
    | (have r₁ := eq12 (σ y) (M.op (M.op X0 (σ y)) (σ x))
       have r₂ := eq889 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq889 X0
       grind)
    | exact resolve eq12 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1793 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) = (k (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq889 eq13
    | (have j0 := eq13 (σ y) (M.op (M.op X0 (σ y)) (σ x))
       grind)
    | exact resolve eq13 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq1798 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1806 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (M.op (M.op X0 (σ y)) (σ x)) ∨ (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) = (k (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1793 X0
       have i₂ := eq634 sF3
       grind)
    | exact superpose eq634 eq1793
    | (have j0 := eq1793 X0
       grind)
    | exact resolve eq1793 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq1807 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ y) = (k (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1798 X0
       have i₂ := eq634 sF3
       grind)
    | exact superpose eq634 eq1798
    | (have j0 := eq1798 X0
       grind)
    | exact resolve eq1798 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq1821 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ y) = (k (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq619 eq1806
    | (have j0 := eq1806 X0
       grind)
    | exact resolve eq1806 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq1806
  have eq1824 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (M.op X0 (σ y)) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1821 X0
       have j1 := eq1807 X0
       grind)
    | (have r₁ := eq1821 X0
       have r₂ := eq1807 X0
       grind)
    | exact resolve eq1821 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807 eq1821
  have eq1842 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1225 eq1824
    | exact resolve eq1824 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225 eq1824
  have eq1845 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1842
  have eq1869 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1845 eq482
    | exact resolve eq482 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq1845
  have eq1874 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1869
       have r₂ := eq608
       grind)
    | exact resolve eq1869 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq1869
  have eq1905 : y = (M.op (M.op y x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq1874
       grind)
    | exact superpose eq1874 eq177
    | exact resolve eq177 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1910 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1874 eq1905
    | exact resolve eq1905 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874 eq1905
  have eq1911 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1910
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1910
    | exact resolve eq1910 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910
  have eq1912 : y = (M.op x y) := by grind
  clear eq1911
  have eq1913 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1912
       grind)
    | exact superpose eq1912 eq18
    | exact resolve eq18 eq1912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1914 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1912
       grind)
    | exact superpose eq1912 eq24
    | exact resolve eq24 eq1912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1912
  have eq1926 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1914 eq20
    | exact resolve eq20 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914
  have eq1986 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1913 eq208
    | exact resolve eq208 eq1913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq2000 : x ≠ x ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq1986 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq1986
       grind)
    | exact resolve eq12 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2001 : x ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1986 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | exact resolve eq13 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq2006 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq2000
  have eq2008 : x ≠ (k (M.op x y) (M.op x y)) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2001
       have i₂ := eq634 sF0
       grind)
    | exact superpose eq634 eq2001
    | exact resolve eq2001 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2009 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq2006
       have i₂ := eq634 sF0
       grind)
    | exact superpose eq634 eq2006
    | exact resolve eq2006 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq2006
  have eq2011 : (M.op x y) = (k (M.op x y) x) ∨ x ≠ (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1913 eq2008
    | exact resolve eq2008 eq1913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913 eq2008
  have eq2012 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq2011
       have r₂ := eq2009
       grind)
    | exact resolve eq2011 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009 eq2011
  have eq2014 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2012 eq40
    | exact resolve eq40 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2012
  have eq2015 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq2014
    | exact resolve eq2014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2014
  have eq2017 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1926 eq2015
    | exact resolve eq2015 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq2023 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2017 eq189
    | exact resolve eq189 eq2017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq2017
  have eq2077 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2023 eq177
    | exact resolve eq177 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2082 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2023 eq2077
    | exact resolve eq2077 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023 eq2077
  have eq2083 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2082
    | exact resolve eq2082 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2082
  have eq2084 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2083
  have eq2085 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2084 eq27
    | exact resolve eq27 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2084
  have eq2096 : False := by grind
  exact eq2096

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pyx_x_pyx_Equation2702 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : x ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (k y x) := by
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
  have eq77 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq36
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0) (σ X1)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq84 y x
       grind)
    | exact superpose eq84 eq90
    | (have j1 := eq84 y x
       grind)
    | exact resolve eq90 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq146 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq167 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq146 eq16
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq84
    | (have j0 := eq84 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq194
    | exact resolve eq194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq198 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq195
       have r₂ := eq27
       grind)
    | exact resolve eq195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq200 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq198
    | exact resolve eq198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq256 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq200 eq51
    | exact resolve eq51 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq266 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq52 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op (M.op (M.op (M.op x y) (M.op y X0)) y) (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) (M.op (σ x) (M.op (σ y) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq256 eq52
    | exact resolve eq52 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq50 eq270
    | exact resolve eq270 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq270
  have eq298 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq256 eq272
    | exact resolve eq272 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq272
  have eq305 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq362 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq200 eq54
    | exact resolve eq54 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq372 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq362 eq362
    | exact resolve eq362 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq378 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq372
  have eq383 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq378 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq481 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq200 eq77
    | (have r₁ := eq77
       have r₂ := eq200
       grind)
    | exact resolve eq77 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq482 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq481
  have eq554 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq107 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq603 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq482 eq383
    | (have j0 := eq383 (σ x)
       grind)
    | exact resolve eq383 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq482
  have eq604 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq603
  have eq609 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq604
       have r₂ := eq378
       grind)
    | exact resolve eq604 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq604
  have eq612 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq609
    | exact resolve eq609 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq681 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq612
    | exact resolve eq612 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq612
  have eq688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq681
  have eq690 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq688
       have r₂ := eq27
       grind)
    | exact resolve eq688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq692 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq690 eq29
    | exact resolve eq29 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq730 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq692
    | exact resolve eq692 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq743 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq835 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730 eq266
    | exact resolve eq266 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq835
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq835
    | exact resolve eq835 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq874 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq730 eq847
    | exact resolve eq847 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq847
  have eq886 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq874
       have r₂ := eq743
       grind)
    | exact resolve eq874 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq1637 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq459 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq459
    | (have j0 := eq459 x X0
       grind)
    | exact resolve eq459 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1641 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq459 X1 X0
       have i₂ := eq84 (σ X1) X0
       grind)
    | exact superpose eq84 eq459
    | (have j1 := eq84 (σ X1) X0
       grind)
    | exact resolve eq459 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq4920 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq554 x y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq554
    | (have j0 := eq554 x y
       grind)
    | exact resolve eq554 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq4957 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4920
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4920
    | exact resolve eq4920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4920
  have eq5011 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4957
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4957
    | exact resolve eq4957 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq5053 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5011
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5011
    | exact resolve eq5011 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5011
  have eq5080 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5053
    | exact resolve eq5053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5053
  have eq35229 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq886
       grind)
    | exact superpose eq886 eq115
    | exact resolve eq115 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq886
  have eq35287 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35229
       have r₂ := eq743
       grind)
    | exact resolve eq35229 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq35229
  have eq35288 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35287
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35287
    | exact resolve eq35287 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35287
  have eq35292 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq35288
       have i₂ := eq84 sF2 sF3
       grind)
    | exact superpose eq84 eq35288
    | (have j1 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq35288 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35288
  have eq45029 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq35292 eq305
    | exact resolve eq305 eq35292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq35292
  have eq45082 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq45029
  have eq45091 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq45082
    | exact resolve eq45082 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45082
  have eq45419 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq200 eq45091
    | exact resolve eq45091 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq45091
  have eq45474 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq45419
  have eq45510 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45474 eq52
    | exact resolve eq52 eq45474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45633 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45474 eq45510
    | exact resolve eq45510 eq45474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45474 eq45510
  have eq45667 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq45633
  have eq45669 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq45667
    | exact resolve eq45667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45667
  have eq45671 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45669 eq27
    | exact resolve eq27 eq45669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45669
  have eq45732 : x = (M.op x y) := by
    first
    | (have r₁ := eq45671
       have r₂ := eq690
       grind)
    | exact resolve eq45671 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq45671
  have eq45734 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq45732 eq20
    | exact resolve eq20 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq45737 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) x) x) := by
    intro X0
    first
    | exact superpose eq45732 eq53
    | exact resolve eq53 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq45739 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ y = (k y x) := by
    first
    | exact superpose eq45732 eq76
    | (have r₁ := eq76
       have r₂ := eq45732
       grind)
    | exact resolve eq76 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq45787 : x = (M.op (M.op x x) x) := by
    first
    | exact superpose eq45732 eq266
    | exact resolve eq266 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq45818 : (M.op x x) = (M.op y y) ∨ y = (k y x) := by grind
  clear eq45739
  have eq45881 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45734
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45734
    | exact resolve eq45734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45734
  have eq45902 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq45881 eq26
    | exact resolve eq26 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq45926 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq45881 eq267
    | exact resolve eq267 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq45981 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45881 eq5080
    | exact resolve eq5080 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080
  have eq46133 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq45981
       have r₂ := eq27
       grind)
    | exact resolve eq45981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45981
  have eq46369 : x = (M.op x x) := by
    first
    | (have i₁ := eq45737 x
       have i₂ := eq45787
       grind)
    | exact superpose eq45787 eq45737
    | exact resolve eq45737 eq45787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45737 eq45787
  have eq46452 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq46369
       grind)
    | exact superpose eq46369 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq46369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51189 : y = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45818
       have i₂ := eq46369
       grind)
    | exact superpose eq46369 eq45818
    | exact resolve eq45818 eq46369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45818 eq46369
  have eq51192 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq51189
       grind)
    | exact superpose eq51189 eq90
    | exact resolve eq90 eq51189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51189
  have eq51245 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq45881 eq51192
    | exact resolve eq51192 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51192
  have eq51264 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51245
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51245
    | exact resolve eq51245 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51245
  have eq51377 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51264 eq84
    | (have j0 := eq84 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq84 eq51264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51264
  have eq51388 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq45902 eq51377
    | exact resolve eq51377 eq45902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51377
  have eq51394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq45902 eq51388
    | exact resolve eq51388 eq45902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51388
  have eq51399 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq51394
       have r₂ := eq27
       grind)
    | exact resolve eq51394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51394
  have eq54200 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46452 y
       have i₂ := eq51399
       grind)
    | exact superpose eq51399 eq46452
    | (have j0 := eq46452 y
       grind)
    | (have r₁ := eq46452 y
       have r₂ := eq51399
       grind)
    | exact resolve eq46452 eq51399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46452 eq51399
  have eq54208 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54200
  have eq54211 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54208
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54208
    | exact resolve eq54208 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54208
  have eq54215 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45732 eq54211
    | exact resolve eq54211 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54211
  have eq54223 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq54215
       grind)
    | exact superpose eq54215 eq90
    | exact resolve eq90 eq54215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq54215
  have eq54297 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45881 eq54223
    | exact resolve eq54223 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54223
  have eq54318 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54297
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54297
    | exact resolve eq54297 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54297
  have eq54337 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45881 eq54318
    | exact resolve eq54318 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54318
  have eq54351 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq54337
       have r₂ := eq46133
       grind)
    | exact resolve eq54337 eq46133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46133 eq54337
  have eq54394 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq54351 eq27
    | exact resolve eq27 eq54351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq54432 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54351 eq45926
    | exact resolve eq45926 eq54351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45926
  have eq54441 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq45902 eq54432
    | exact resolve eq54432 eq45902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45902 eq54432
  have eq54454 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq54351 eq54441
    | exact resolve eq54441 eq54351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54351 eq54441
  have eq64302 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1641 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1641
    | (have j0 := eq1641 X0 x
       grind)
    | exact resolve eq1641 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq64427 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ (M.op x y)))) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq45881 eq64302
    | (have j0 := eq64302 X0
       grind)
    | exact resolve eq64302 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64302
  have eq64520 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op X0 (σ (M.op x y)))) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq64427 X0
       have i₂ := eq1637 X0
       grind)
    | exact superpose eq1637 eq64427
    | (have j0 := eq64427 X0
       grind)
    | exact resolve eq64427 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637 eq64427
  have eq64588 : ∀ X0 : G, (τ (k (σ (M.op x y)) X0)) = (τ (M.op X0 (σ (M.op x y)))) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq45881 eq64520
    | (have j0 := eq64520 X0
       grind)
    | exact resolve eq64520 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64520
  have eq64635 : ∀ X0 : G, (τ (k (σ (M.op x y)) X0)) = (τ (M.op X0 (σ (M.op x y)))) ∨ (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq45881 eq64588
    | (have j0 := eq64588 X0
       grind)
    | exact resolve eq64588 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64588
  have eq65019 : (k (M.op x y) y) = (τ (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq64635 eq167
    | (have j1 := eq64635 (σ y)
       grind)
    | exact resolve eq167 eq64635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167 eq64635
  have eq65128 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq54454 eq65019
    | exact resolve eq65019 eq54454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65019
  have eq65153 : (τ (σ (M.op x y))) = (k x y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq45732 eq65128
    | exact resolve eq65128 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65128
  have eq65165 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq30 eq65153
    | exact resolve eq65153 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq65153
  have eq65173 : x = (k x y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq45732 eq65165
    | exact resolve eq65165 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65165
  have eq65175 : (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq54454 eq65173
    | exact resolve eq65173 eq54454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54454 eq65173
  have eq65177 : x = (k x y) := by
    first
    | (have r₁ := eq65175
       have r₂ := eq54394
       grind)
    | exact resolve eq65175 eq54394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65175
  have eq65180 : y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq65177
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq65177
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq65177 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq65177
  have eq65536 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq279 x
       have i₂ := eq65180
       grind)
    | exact superpose eq65180 eq279
    | exact resolve eq279 eq65180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq65180
  have eq65609 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq45732 eq65536
    | exact resolve eq65536 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65536
  have eq65623 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq65609
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65609
    | exact resolve eq65609 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65609
  have eq65634 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq45732 eq65623
    | exact resolve eq65623 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65623
  have eq65635 : x = (M.op y x) := by grind
  clear eq65634
  have eq65823 : y = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq65635
       grind)
    | exact superpose eq65635 eq52
    | exact resolve eq52 eq65635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65854 : y = (M.op x y) := by
    first
    | (have i₁ := eq65823
       have i₂ := eq65635
       grind)
    | exact superpose eq65635 eq65823
    | exact resolve eq65823 eq65635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65635 eq65823
  have eq65880 : y = (M.op x y) := by
    first
    | (have i₁ := eq65854
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65854
    | exact resolve eq65854 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq65854
  have eq65900 : x = y := by
    first
    | exact superpose eq45732 eq65880
    | exact resolve eq65880 eq45732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45732 eq65880
  have eq65930 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq65900
       grind)
    | exact superpose eq65900 eq24
    | exact resolve eq24 eq65900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq65900
  have eq66221 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq65930
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq65930
    | exact resolve eq65930 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq65930
  have eq66290 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq45881 eq66221
    | exact resolve eq66221 eq45881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45881 eq66221
  have eq66351 : False := by grind
  exact eq66351

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_pyx_y_pyx_Equation2702 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
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
  clear eq41
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
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
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
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
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
  have eq597 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (k X0 X1)) X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X1 (M.op (M.op X2 X1) (k X0 X1))
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq596
       grind)
    | exact superpose eq596 eq40
    | exact resolve eq40 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq639
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq639
    | exact resolve eq639 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq642 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq640
    | exact resolve eq640 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq597
    | exact resolve eq597 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq650
       have r₂ := eq27
       grind)
    | exact resolve eq650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq664 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq657 eq187
    | exact resolve eq187 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq664
    | exact resolve eq664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq670 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq657 eq668
    | exact resolve eq668 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq683 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k y x) := by
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
  have eq685 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq670 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq670
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq670
       grind)
    | exact resolve eq12 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq708
  have eq785 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq712 eq91
    | exact resolve eq91 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq789 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq785
    | exact resolve eq785 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq785
  have eq796 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq789 eq181
    | exact resolve eq181 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq805 : (σ x) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq670 eq796
    | exact resolve eq796 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq796
  have eq816 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq805 eq153
    | exact resolve eq153 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq805
  have eq821 : y = (k x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq816
    | exact resolve eq816 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq1297 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq657 eq685
    | (have r₁ := eq685
       have r₂ := eq657
       grind)
    | exact resolve eq685 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq685
  have eq1298 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1297
  have eq1299 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq1298
    | exact resolve eq1298 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1310 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1299 eq181
    | exact resolve eq181 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq1326 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1310
    | exact resolve eq1310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq1326
    | exact resolve eq1326 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq1326
  have eq1334 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1332
       have r₂ := eq27
       grind)
    | exact resolve eq1332 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1336 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1334 eq29
    | exact resolve eq29 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1340 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1334 eq117
    | exact resolve eq117 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1334
  have eq1353 : (k y x) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115 eq1340
    | exact resolve eq1340 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1340
  have eq1357 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1336
    | exact resolve eq1336 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq1359 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq596 eq1353
    | exact resolve eq1353 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq1353
  have eq1361 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1357
       grind)
    | exact superpose eq1357 eq18
    | exact resolve eq18 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1362 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1357
       grind)
    | exact superpose eq1357 eq24
    | exact resolve eq24 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1366 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq683
       have i₂ := eq1357
       grind)
    | exact superpose eq1357 eq683
    | (have r₁ := eq683
       have r₂ := eq1357
       grind)
    | exact resolve eq683 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq1367 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1366
  have eq1370 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1362
    | exact resolve eq1362 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1405 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1361 eq186
    | exact resolve eq186 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1433 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1405 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq1405
       grind)
    | exact resolve eq12 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1437 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1433
  have eq1770 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1367 eq38
    | exact resolve eq38 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1775 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1770
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1770
    | exact resolve eq1770 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq1777 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq1775
    | exact resolve eq1775 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775
  have eq1782 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1777 eq597
    | exact resolve eq597 eq1777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1798 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1437 eq36
    | exact resolve eq36 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1437
  have eq1802 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1798
    | exact resolve eq1798 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq1804 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq1802
    | exact resolve eq1802 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq1831 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1804 eq635
    | (have j0 := eq635 (σ y) (σ x)
       grind)
    | exact resolve eq635 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1979 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) y) y) ∨ x = (M.op y x) ∨ x = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq601 x y X0
       have i₂ := eq821
       grind)
    | exact superpose eq821 eq601
    | (have j0 := eq601 y (M.op (M.op X0 y) y) x
       grind)
    | exact resolve eq601 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq821
  have eq2033 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) y) y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1979 X0
       have j1 := eq635 (M.op (M.op X0 y) y) y
       grind)
    | (have r₁ := eq1979 X0
       have r₂ := eq635 y x
       grind)
    | exact resolve eq1979 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq2045 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1357 eq2033
    | (have j0 := eq2033 X0
       grind)
    | exact resolve eq2033 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357 eq2033
  have eq2386 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1782 eq181
    | exact resolve eq181 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq2399 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1361 eq2386
    | exact resolve eq2386 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361 eq2386
  have eq2439 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2399 eq40
    | exact resolve eq40 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2399
  have eq2449 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2439
    | exact resolve eq2439 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2451 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq2449
    | exact resolve eq2449 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq2477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2451 eq597
    | exact resolve eq597 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq2451
  have eq2488 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2477
  have eq2500 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2488 eq27
    | exact resolve eq27 eq2488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2511 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2500
       have r₂ := eq1370
       grind)
    | exact resolve eq2500 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq2516 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2511 eq27
    | exact resolve eq27 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2517 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2511 eq176
    | exact resolve eq176 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2518 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2511 eq179
    | exact resolve eq179 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2519 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2511 eq187
    | exact resolve eq187 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq2525 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2519
       have i₂ := eq181 sF2
       grind)
    | exact superpose eq181 eq2519
    | exact resolve eq2519 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq2526 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq2516
    | exact resolve eq2516 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq2516
  have eq2529 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq2526
  have eq2536 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2525 eq91
    | exact resolve eq91 eq2525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq2525
  have eq2543 : x = (k x (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2536
    | exact resolve eq2536 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2536
  have eq2556 : x ≠ x ∨ x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2543 eq635
    | (have j0 := eq635 (τ (M.op (σ x) (σ x))) x
       grind)
    | (have r₁ := eq635 (τ (M.op (σ x) (σ x))) x
       have r₂ := eq2543
       grind)
    | exact resolve eq635 eq2543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543
  have eq2557 : x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by grind
  clear eq2556
  have eq2581 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (k X0 (σ y))) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2517 X0
       have i₂ := eq28 X0 sF3
       grind)
    | exact superpose eq28 eq2517
    | (have j1 := eq28 (σ y) (M.op (σ x) (k X0 (σ y)))
       grind)
    | exact resolve eq2517 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2618 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2518 eq2518
    | exact resolve eq2518 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518
  have eq2634 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2618
  have eq2656 : x = (M.op (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2634 eq2557
    | exact resolve eq2557 eq2634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2672 : x = (M.op (τ (σ x)) x) ∨ x = (M.op x y) := by grind
  clear eq2656
  have eq2678 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2672
    | exact resolve eq2672 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2672
  have eq4740 : y = (M.op (M.op (M.op x y) y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2045 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2045
    | (have j0 := eq2045 x
       grind)
    | exact resolve eq2045 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq4943 : y = (M.op (k y (M.op x y)) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4740
       have i₂ := eq28 y sF0
       grind)
    | exact superpose eq28 eq4740
    | (have j1 := eq28 y (k y (M.op x y))
       grind)
    | exact resolve eq4740 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4740
  have eq4967 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1359 eq4943
    | exact resolve eq4943 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943
  have eq4968 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq4967
  have eq4981 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4968 eq177
    | exact resolve eq177 eq4968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4993 : y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4968 eq4981
    | exact resolve eq4981 eq4968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4968 eq4981
  have eq4994 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq4993
  have eq8018 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1804 eq2581
    | (have j0 := eq2581 (σ x)
       grind)
    | exact resolve eq2581 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq2581
  have eq8053 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq8018
  have eq8058 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq8053
    | exact resolve eq8053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8053
  have eq8061 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2511 eq8058
    | exact resolve eq8058 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8058
  have eq8062 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq8061
    | exact resolve eq8061 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061
  have eq8063 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2511 eq8062
    | exact resolve eq8062 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8062
  have eq8064 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq8063
       have r₂ := eq1831
       grind)
    | exact resolve eq8063 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831 eq8063
  have eq8069 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq8064 eq2517
    | exact resolve eq2517 eq8064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517 eq8064
  have eq8107 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq8069
  have eq8127 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2634 eq8107
    | exact resolve eq8107 eq2634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634 eq8107
  have eq8131 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq8127
    | exact resolve eq8127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8127
  have eq8135 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2511 eq8131
    | exact resolve eq8131 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511 eq8131
  have eq8138 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8135
       have r₂ := eq2529
       grind)
    | exact resolve eq8135 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529 eq8135
  have eq8144 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2678
       have i₂ := eq8138
       grind)
    | exact superpose eq8138 eq2678
    | exact resolve eq2678 eq8138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678 eq8138
  have eq8174 : x = (M.op x y) := by grind
  clear eq8144
  have eq8182 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8174
       grind)
    | exact superpose eq8174 eq18
    | exact resolve eq18 eq8174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8183 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq8174
       grind)
    | exact superpose eq8174 eq22
    | exact resolve eq22 eq8174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8174
  have eq8196 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8183 eq20
    | exact resolve eq20 eq8183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8267 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8182 eq4994
    | exact resolve eq4994 eq8182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq8284 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq8182 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | exact resolve eq12 eq8182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8182
  have eq8300 : y = (M.op x y) := by grind
  clear eq8267
  have eq8305 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have r₁ := eq8284
       have r₂ := eq1359
       grind)
    | exact resolve eq8284 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359 eq8284
  have eq8309 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq8305
       have i₂ := eq8300
       grind)
    | exact superpose eq8300 eq8305
    | exact resolve eq8305 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8305
  have eq8311 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8309
       have i₂ := eq8300
       grind)
    | exact superpose eq8300 eq8309
    | exact resolve eq8309 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8309
  have eq8312 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq635 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq8311
       have r₂ := eq635 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq8311 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq8311
  have eq8314 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8300
       grind)
    | exact superpose eq8300 eq24
    | exact resolve eq24 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8300
  have eq8325 : (σ x) = (σ y) := by
    first
    | exact superpose eq8183 eq8314
    | exact resolve eq8314 eq8183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8183 eq8314
  have eq8327 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8325 eq26
    | exact resolve eq26 eq8325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8325
  have eq8463 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8312 eq181
    | exact resolve eq181 eq8312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq8481 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8312 eq8463
    | exact resolve eq8463 eq8312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8312 eq8463
  have eq8489 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8481 eq38
    | exact resolve eq38 eq8481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq8481
  have eq8501 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq8489
    | exact resolve eq8489 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8489
  have eq8503 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq8196 eq8501
    | exact resolve eq8501 eq8196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8501
  have eq8510 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8327
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq8327
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq8327 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8560 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8503 eq8510
    | exact resolve eq8510 eq8503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8503 eq8510
  have eq8561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8327 eq8560
    | exact resolve eq8560 eq8327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8327 eq8560
  have eq8562 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8561
  have eq8565 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8562 eq27
    | exact resolve eq27 eq8562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8562
  have eq8581 : False := by grind
  exact eq8581

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq250 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq263 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq251 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq268 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq263 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq263 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq263 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq269 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq250 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq250 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq268
    | (have j0 := eq268 X0 X1
       grind)
    | exact resolve eq268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq278 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq279 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq269
    | (have j0 := eq269 X0 X1
       grind)
    | exact resolve eq269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq280 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       have j1 := eq278 X0 X1
       grind)
    | (have r₁ := eq280 X0 X1
       have r₂ := eq278 X0 X1
       grind)
    | exact resolve eq280 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq280
  have eq286 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq285
    | exact resolve eq285 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq285 x y
       grind)
    | exact superpose eq285 eq16
    | exact resolve eq16 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq360 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq286 X0 (τ X1)
       grind)
    | exact superpose eq286 eq18
    | exact resolve eq18 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq286
  have eq373 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq360
    | exact resolve eq360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq379 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq373
    | exact resolve eq373 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq397 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq297
       have i₂ := eq379 x y
       grind)
    | exact superpose eq379 eq297
    | exact resolve eq297 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq379
  have eq398 : False := by grind
  exact eq398

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation413 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq106 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  clear eq19
  have eq114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq544 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
  have eq574 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq580 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq574 X1 X0
       grind)
    | exact superpose eq574 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq574 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq574 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq574 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq574 X0 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq574 X1 X0
       grind)
    | exact superpose eq574 eq9
    | (have j1 := eq574 X1 X0
       grind)
    | exact resolve eq9 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq596 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq768 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq16
    | (have j1 := eq114 x y
       grind)
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4101 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq581 X0 X1
       grind)
    | exact superpose eq581 eq9
    | (have j1 := eq581 X0 X1
       grind)
    | exact resolve eq9 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq4137 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0
       have i₂ := eq4101 (τ X0) X1
       grind)
    | exact superpose eq4101 eq30
    | (have j1 := eq4101 (τ X0) X1
       grind)
    | exact resolve eq30 eq4101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4101
  have eq4148 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4137 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4137
    | (have j0 := eq4137 X0 X1
       grind)
    | exact resolve eq4137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq4154 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4148 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4148
    | (have j0 := eq4148 X0 X1
       grind)
    | exact resolve eq4148 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4148
  have eq4203 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0
       have i₂ := eq4154 (σ X0) X1
       grind)
    | exact superpose eq4154 eq22
    | (have j1 := eq4154 (σ X0) X1
       grind)
    | exact resolve eq22 eq4154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4154
  have eq4216 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4203 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4203
    | (have j0 := eq4203 X0 X1
       grind)
    | exact resolve eq4203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203
  have eq4223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4216 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4216
    | (have j0 := eq4216 X0 X1
       grind)
    | exact resolve eq4216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216
  have eq4228 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4223 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4223
    | (have j0 := eq4223 X0 X1
       grind)
    | exact resolve eq4223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223
  have eq6112 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq768
       have i₂ := eq596 y x
       grind)
    | exact superpose eq596 eq768
    | (have j1 := eq596 y x
       grind)
    | (have r₁ := eq768
       have r₂ := eq596 y x
       grind)
    | (have r₁ := eq768
       have r₂ := eq596 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq768
       have r₂ := eq596 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq768 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq6113 : x = y ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6112
  have eq16568 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6113
       grind)
    | exact superpose eq6113 eq16
    | exact resolve eq16 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq16569 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16568
       have r₂ := eq22 x
       grind)
    | exact resolve eq16568 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16568
  have eq16576 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq775 x y
       have i₂ := eq16569
       grind)
    | exact superpose eq16569 eq775
    | (have j0 := eq775 x y
       grind)
    | exact resolve eq775 eq16569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq16569
  have eq16587 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq16576
  have eq16591 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16587
       grind)
    | exact superpose eq16587 eq16
    | exact resolve eq16 eq16587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16587
  have eq16620 : (σ y) ≠ (σ y) ∨ (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16591
       have i₂ := eq574 x y
       grind)
    | exact superpose eq574 eq16591
    | (have j1 := eq574 x y
       grind)
    | (have r₁ := eq16591
       have r₂ := eq574 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq16591
       have r₂ := eq574 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq16591
       have r₂ := eq574 (σ y) (σ (M.op y y))
       grind)
    | exact resolve eq16591 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq16591
  have eq16621 : (σ y) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ x = y := by grind
  clear eq16620
  have eq16629 : x = y ∨ (σ (M.op x y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq4228 y x
       grind)
    | (have r₁ := eq16621
       have r₂ := eq4228 y x
       grind)
    | (have r₁ := eq16621
       have r₂ := eq4228 (σ y) (σ (M.op y y))
       grind)
    | (have r₁ := eq16621
       have r₂ := eq4228 (σ (M.op y y)) (σ y)
       grind)
    | exact resolve eq16621 eq4228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228 eq16621
  have eq16630 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16629
       grind)
    | exact superpose eq16629 eq16
    | exact resolve eq16 eq16629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16629
  have eq16631 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq16630
       have r₂ := eq22 x
       grind)
    | exact resolve eq16630 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16630
  have eq16784 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16631
       grind)
    | exact superpose eq16631 eq10
    | exact resolve eq10 eq16631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16631
  have eq16846 : x = y ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16784
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16784
    | exact resolve eq16784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16784
  have eq16848 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16846
       grind)
    | exact superpose eq16846 eq16
    | exact resolve eq16 eq16846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16846
  have eq16849 : (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq16848
       have r₂ := eq22 x
       grind)
    | exact resolve eq16848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16848
  have eq16855 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq768
       have i₂ := eq16849
       grind)
    | exact superpose eq16849 eq768
    | (have r₁ := eq768
       have r₂ := eq16849
       grind)
    | exact resolve eq768 eq16849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq16903 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16855
  have eq16942 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16903
       grind)
    | exact superpose eq16903 eq16
    | exact resolve eq16 eq16903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16945 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq16903
       grind)
    | exact superpose eq16903 eq9
    | exact resolve eq9 eq16903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16946 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq16903
       grind)
    | exact superpose eq16903 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16903
       grind)
    | exact resolve eq13 eq16903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16903
  have eq16950 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq16946
  have eq16951 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq16950
  have eq16958 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16951
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq16951
    | exact resolve eq16951 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16951
  have eq16959 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq16945
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq16945
    | exact resolve eq16945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16945
  have eq16964 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16958
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16958
    | exact resolve eq16958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16958
  have eq16966 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16964
       have i₂ := eq16849
       grind)
    | exact superpose eq16849 eq16964
    | exact resolve eq16964 eq16849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16849 eq16964
  have eq17714 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16966
       grind)
    | exact superpose eq16966 eq10
    | exact resolve eq10 eq16966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16966
  have eq17776 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq17714
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17714
    | exact resolve eq17714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17714
  have eq17778 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17776
       grind)
    | exact superpose eq17776 eq16
    | exact resolve eq16 eq17776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17776
  have eq17785 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq17778
       have r₂ := eq22 x
       grind)
    | exact resolve eq17778 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17778
  have eq17817 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq106 y
       have i₂ := eq17785
       grind)
    | exact superpose eq17785 eq106
    | exact resolve eq106 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq17840 : (M.op y y) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq17785
       grind)
    | exact superpose eq17785 eq10
    | exact resolve eq10 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17902 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq17840
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq17840
    | exact resolve eq17840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840
  have eq23938 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16959
       grind)
    | exact superpose eq16959 eq16
    | exact resolve eq16 eq16959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23943 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq16959
       grind)
    | exact superpose eq16959 eq22
    | exact resolve eq22 eq16959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16959
  have eq24018 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq23943
       have i₂ := eq17785
       grind)
    | exact superpose eq17785 eq23943
    | exact resolve eq23943 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23943
  have eq24023 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq23938
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq23938
    | exact resolve eq23938 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23938
  have eq24046 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq24018
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq24018
    | exact resolve eq24018 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24018
  have eq24050 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24023
       have i₂ := eq17785
       grind)
    | exact superpose eq17785 eq24023
    | exact resolve eq24023 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24023
  have eq24052 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24046
       have i₂ := eq17785
       grind)
    | exact superpose eq17785 eq24046
    | exact resolve eq24046 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24046
  have eq24053 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have r₁ := eq24052
       have r₂ := eq24050
       grind)
    | exact resolve eq24052 eq24050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24050 eq24052
  have eq24090 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17817
       have i₂ := eq24053
       grind)
    | exact superpose eq24053 eq17817
    | exact resolve eq17817 eq24053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17817 eq24053
  have eq24123 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq24090
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq24090
    | exact resolve eq24090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24090
  have eq24142 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24123
       have i₂ := eq17902
       grind)
    | exact superpose eq17902 eq24123
    | exact resolve eq24123 eq17902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17902 eq24123
  have eq24180 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16942
       have i₂ := eq24142
       grind)
    | exact superpose eq24142 eq16942
    | (have r₁ := eq16942
       have r₂ := eq24142
       grind)
    | exact resolve eq16942 eq24142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16942
  have eq24229 : (σ x) = (σ y) := by grind
  clear eq24180
  have eq24265 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24229
       grind)
    | exact superpose eq24229 eq16
    | exact resolve eq16 eq24229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24271 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq24229
       grind)
    | exact superpose eq24229 eq22
    | exact resolve eq22 eq24229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24336 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24271
       have i₂ := eq17785
       grind)
    | exact superpose eq17785 eq24271
    | exact resolve eq24271 eq17785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17785 eq24271
  have eq24342 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24265
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq24265
    | exact resolve eq24265 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24265
  have eq24347 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24336
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq24336
    | exact resolve eq24336 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24336
  have eq24350 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24342
       have i₂ := eq24142
       grind)
    | exact superpose eq24142 eq24342
    | exact resolve eq24342 eq24142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24342
  have eq24355 : (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24347
       have i₂ := eq24142
       grind)
    | exact superpose eq24142 eq24347
    | exact resolve eq24347 eq24142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24142 eq24347
  have eq24358 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24350
       have i₂ := eq24229
       grind)
    | exact superpose eq24229 eq24350
    | exact resolve eq24350 eq24229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24350
  have eq24362 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24355
       have i₂ := eq24229
       grind)
    | exact superpose eq24229 eq24355
    | exact resolve eq24355 eq24229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24229 eq24355
  have eq24367 : False := by grind
  exact eq24367

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = Y then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyy_y_pxy_pyx_pyy_Equation418 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq345 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq357 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq345 (τ X0) X1
       grind)
    | exact superpose eq345 eq18
    | (have j1 := eq345 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq360 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq345 (σ X0) (σ X1)
       grind)
    | exact superpose eq345 eq15
    | (have j1 := eq345 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq423 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq357 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq357
    | exact resolve eq357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq463 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq423
    | (have j0 := eq423 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq423 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq584 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq360 x y
       grind)
    | exact superpose eq360 eq16
    | (have j1 := eq360 x y
       grind)
    | exact resolve eq16 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq597 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq584
       have i₂ := eq463 x y
       grind)
    | exact superpose eq463 eq584
    | (have j1 := eq463 (σ x) (σ y)
       grind)
    | (have r₁ := eq584
       have r₂ := eq463 x y
       grind)
    | (have r₁ := eq584
       have r₂ := eq463 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq584
       have r₂ := eq463 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq584 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq584
  have eq598 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq597
  have eq621 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq598
       grind)
    | exact superpose eq598 eq16
    | exact resolve eq16 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq622 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq621
       have i₂ := eq63 (σ x)
       grind)
    | exact superpose eq63 eq621
    | exact resolve eq621 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq623 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq622
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq622
    | exact resolve eq622 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq624 : (σ x) = (σ y) := by grind
  clear eq623
  have eq625 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq624
       grind)
    | exact superpose eq624 eq16
    | exact resolve eq16 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq624
       grind)
    | exact superpose eq624 eq10
    | exact resolve eq10 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq663 : x = y := by
    first
    | (have i₁ := eq626
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq626
    | exact resolve eq626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq664 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq625
       have i₂ := eq63 (σ x)
       grind)
    | exact superpose eq63 eq625
    | exact resolve eq625 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq665 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq664
       have i₂ := eq663
       grind)
    | exact superpose eq663 eq664
    | exact resolve eq664 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq664
  have eq666 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq665
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq665
    | exact resolve eq665 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq665
  have eq667 : False := by grind
  exact eq667
