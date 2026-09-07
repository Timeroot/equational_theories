import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq45 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq47 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq47 (σ X0) (σ X1)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq47 (τ X0) X1
       grind)
    | exact superpose eq47 eq17
    | (have j1 := eq47 (τ X0) X1
       grind)
    | exact resolve eq17 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq47
  have eq252 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq67
    | exact resolve eq67 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq281 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq252
    | (have j0 := eq252 X0 X1
       grind)
    | exact resolve eq252 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq454 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq14
    | (have j1 := eq63 x y
       grind)
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq767 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq773 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq459 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq459
    | (have j0 := eq459 (τ X1) (τ X0)
       grind)
    | exact resolve eq459 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq773 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq773
    | (have j0 := eq773 X0 X1
       grind)
    | exact resolve eq773 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq784 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq782
    | (have j0 := eq782 X0 X1
       grind)
    | exact resolve eq782 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq785 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq784 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq784
    | (have j0 := eq784 X0 X1
       grind)
    | exact resolve eq784 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq786 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq785
    | (have j0 := eq785 X0 X1
       grind)
    | exact resolve eq785 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq876 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq786 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq786
    | (have j0 := eq786 (τ X0) (τ X1)
       grind)
    | exact resolve eq786 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq786
  have eq1839 : ∀ X0 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq876
  have eq1889 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq454
       have i₂ := eq281 x y
       grind)
    | exact superpose eq281 eq454
    | (have j1 := eq281 (σ x) (σ y)
       grind)
    | (have r₁ := eq454
       have r₂ := eq281 x y
       grind)
    | exact resolve eq454 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq1890 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1889
  have eq1894 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1890
       grind)
    | exact superpose eq1890 eq14
    | exact resolve eq14 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1895 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq1890
       grind)
    | exact superpose eq1890 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1890
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq1890
       grind)
    | exact resolve eq11 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1895
  have eq1897 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1896
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq1896
    | exact resolve eq1896 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq15385 : (τ (σ y)) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1839 (σ y)
       have i₂ := eq1897
       grind)
    | exact superpose eq1897 eq1839
    | exact resolve eq1839 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839 eq1897
  have eq15396 : y ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15385
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq15385
    | exact resolve eq15385 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15385
  have eq15412 : y = (M.op (τ (σ x)) y) ∨ y ≠ (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15396
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq15396
    | exact resolve eq15396 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15396
  have eq15422 : y = (M.op x y) ∨ y ≠ (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15412
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq15412
    | exact resolve eq15412 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15412
  have eq15423 : y ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq15422
  have eq22286 : y ≠ (τ (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15423
       have i₂ := eq1890
       grind)
    | exact superpose eq1890 eq15423
    | exact resolve eq15423 eq1890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890 eq15423
  have eq22294 : y ≠ (τ (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq22286
  have eq22298 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22294
       have r₂ := eq8 y
       grind)
    | exact resolve eq22294 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22294
  have eq22586 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq281 x y
       have i₂ := eq22298
       grind)
    | exact superpose eq22298 eq281
    | (have j0 := eq281 x y
       grind)
    | exact resolve eq281 eq22298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq22298
  have eq22663 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq22586
  have eq22690 : y = (M.op x y) := by
    first
    | (have r₁ := eq22663
       have r₂ := eq1894
       grind)
    | exact resolve eq22663 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq22663
  have eq23046 : y ≠ y ∨ x = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq22690
       grind)
    | exact superpose eq22690 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq22690
       grind)
    | exact resolve eq11 eq22690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23047 : y = (k y x) ∨ x = (M.op y y) := by grind
  clear eq23046
  have eq23333 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq459 x y
       have i₂ := eq23047
       grind)
    | exact superpose eq23047 eq459
    | (have j0 := eq459 x y
       grind)
    | exact resolve eq459 eq23047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq23047
  have eq23360 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq23333
  have eq23954 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq23360
       grind)
    | exact superpose eq23360 eq14
    | exact resolve eq14 eq23360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23360
  have eq23958 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23954
       have i₂ := eq22690
       grind)
    | exact superpose eq22690 eq23954
    | exact resolve eq23954 eq22690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23954
  have eq23959 : x = (M.op y y) := by grind
  clear eq23958
  have eq24283 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq767 y
       have i₂ := eq23959
       grind)
    | exact superpose eq23959 eq767
    | exact resolve eq767 eq23959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq23959
  have eq24294 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24283
       have i₂ := eq22690
       grind)
    | exact superpose eq22690 eq24283
    | exact resolve eq24283 eq22690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24283
  have eq24295 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24294
  have eq25510 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq24295
       grind)
    | exact superpose eq24295 eq14
    | exact resolve eq14 eq24295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24295
  have eq25514 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq25510
       have i₂ := eq22690
       grind)
    | exact superpose eq22690 eq25510
    | exact resolve eq25510 eq22690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22690 eq25510
  have eq25515 : False := by grind
  exact eq25515

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
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
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq47 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq47 (σ X0) (σ X1)
       grind)
    | exact superpose eq47 eq13
    | (have j1 := eq47 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq47 X0 (τ X1)
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 X0 (τ X1)
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq47
  have eq252 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq65
    | exact resolve eq65 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq281 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq252
    | (have j0 := eq252 X0 X1
       grind)
    | exact resolve eq252 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq454 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq14
    | (have j1 := eq63 x y
       grind)
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1974 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq454
       have i₂ := eq281 y x
       grind)
    | exact superpose eq281 eq454
    | (have j1 := eq281 (σ y) (σ x)
       grind)
    | (have r₁ := eq454
       have r₂ := eq281 y x
       grind)
    | exact resolve eq454 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq1975 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1974
  have eq1979 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1975
       grind)
    | exact superpose eq1975 eq14
    | exact resolve eq14 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1980 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq1975
       grind)
    | exact superpose eq1975 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1975
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq1975
       grind)
    | exact resolve eq11 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1981 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1980
  have eq1982 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1981
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq1981
    | exact resolve eq1981 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq14668 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq1982
  have eq14677 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14668
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq14668
    | exact resolve eq14668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14668
  have eq62482 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1975
       have i₂ := eq14677
       grind)
    | exact superpose eq14677 eq1975
    | exact resolve eq1975 eq14677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975 eq14677
  have eq62490 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq62482
  have eq63379 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq281 y x
       have i₂ := eq62490
       grind)
    | exact superpose eq62490 eq281
    | (have j0 := eq281 y x
       grind)
    | exact resolve eq281 eq62490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq62490
  have eq63458 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq63379
  have eq63485 : x = (M.op x y) := by
    first
    | (have r₁ := eq63458
       have r₂ := eq1979
       grind)
    | exact resolve eq63458 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979 eq63458
  have eq64423 : x ≠ x ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq63485
       grind)
    | exact superpose eq63485 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq63485
       grind)
    | exact resolve eq11 eq63485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64424 : x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq64423
  have eq65337 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq459 x y
       have i₂ := eq64424
       grind)
    | exact superpose eq64424 eq459
    | (have j0 := eq459 x y
       grind)
    | exact resolve eq459 eq64424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64424
  have eq65393 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq65337
  have eq67261 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65393
       grind)
    | exact superpose eq65393 eq14
    | exact resolve eq14 eq65393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65393
  have eq67267 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67261
       have i₂ := eq63485
       grind)
    | exact superpose eq63485 eq67261
    | exact resolve eq67261 eq63485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67261
  have eq67268 : x = (M.op y y) := by grind
  clear eq67267
  have eq68207 : (M.op x y) = (k y x) := by grind
  clear eq67268
  have eq68218 : x = (k y x) := by
    first
    | (have i₁ := eq68207
       have i₂ := eq63485
       grind)
    | exact superpose eq63485 eq68207
    | exact resolve eq68207 eq63485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68207
  have eq69213 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq459 x y
       have i₂ := eq68218
       grind)
    | exact superpose eq68218 eq459
    | (have j0 := eq459 x y
       grind)
    | exact resolve eq459 eq68218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq68218
  have eq69269 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq69213
  have eq71238 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69269
       grind)
    | exact superpose eq69269 eq14
    | exact resolve eq14 eq69269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69269
  have eq71244 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq71238
       have i₂ := eq63485
       grind)
    | exact superpose eq63485 eq71238
    | exact resolve eq71238 eq63485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63485 eq71238
  have eq71245 : False := by grind
  exact eq71245

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq57 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq58 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq181 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0
       have i₂ := eq38 X0 X1
       grind)
    | (have i₁ := eq58 X0
       have i₂ := eq38 X0 (M.op X0 X0)
       grind)
    | exact superpose eq38 eq58
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq58 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq193 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq317 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq193 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq318 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq317 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq318 (σ X0)
       grind)
    | exact superpose eq318 eq13
    | exact resolve eq13 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq389 X0
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq389
    | exact resolve eq389 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq389
  have eq491 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq8
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq8 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq547 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq491 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq491
    | (have j0 := eq491 X0 X1
       grind)
    | exact resolve eq491 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq620 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq547
    | (have j0 := eq547 X0 X1
       grind)
    | exact resolve eq547 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq664 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq396 X1
       grind)
    | exact superpose eq396 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq928 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq934 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 (σ X0)
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq58
    | exact resolve eq58 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq939 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq934 X0
       have i₂ := eq13 (M.op X0 X0) X0
       grind)
    | exact superpose eq13 eq934
    | exact resolve eq934 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq941 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq928 X0
       have i₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact superpose eq13 eq928
    | exact resolve eq928 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq949 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq939 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq939
    | exact resolve eq939 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq939
  have eq951 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq941
  have eq5191 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq664 X0 X1
       grind)
    | (have i₁ := eq8 X0
       have i₂ := eq664 X0 X1
       grind)
    | exact superpose eq664 eq8
    | (have j1 := eq664 X0 X1
       grind)
    | exact resolve eq8 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq5400 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5191 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq5191
    | (have j0 := eq5191 X0 X1
       grind)
    | exact resolve eq5191 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5191
  have eq6806 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq40
    | exact resolve eq40 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq7204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6806 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq6806
    | (have j0 := eq6806 X0 X1
       grind)
    | exact resolve eq6806 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6806
  have eq85165 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5400 x y
       grind)
    | exact superpose eq5400 eq14
    | (have j1 := eq5400 x y
       grind)
    | exact resolve eq14 eq5400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5400
  have eq85256 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq7204 x y
       grind)
    | (have r₁ := eq85165
       have r₂ := eq7204 y x
       grind)
    | exact resolve eq85165 eq7204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7204 eq85165
  have eq88786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq949 y
       have i₂ := eq85256
       grind)
    | exact superpose eq85256 eq949
    | exact resolve eq949 eq85256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq85256
  have eq88817 : y = (M.op x x) := by
    first
    | (have r₁ := eq88786
       have r₂ := eq14
       grind)
    | exact resolve eq88786 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88786
  have eq91592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq951 x
       have i₂ := eq88817
       grind)
    | exact superpose eq88817 eq951
    | exact resolve eq951 eq88817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq88817
  have eq91627 : False := by grind
  exact eq91627

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq57 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq180 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0
       have i₂ := eq38 X0 X1
       grind)
    | (have i₁ := eq58 X0
       have i₂ := eq38 X0 (M.op X0 X0)
       grind)
    | exact superpose eq38 eq58
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq58 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq192 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq314 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq192 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq314 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq382 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq315 (σ X0)
       grind)
    | exact superpose eq315 eq13
    | exact resolve eq13 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq382 X0
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq382
    | exact resolve eq382 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq382
  have eq484 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq8
    | (have j1 := eq39 X1 X0
       grind)
    | exact resolve eq8 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq540 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq484
    | (have j0 := eq484 X0 X1
       grind)
    | exact resolve eq484 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq613 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq540
    | (have j0 := eq540 X0 X1
       grind)
    | exact resolve eq540 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq657 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq389 X1
       grind)
    | exact superpose eq389 eq613
    | (have j0 := eq613 X0 X1
       grind)
    | exact resolve eq613 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq917 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq923 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 (σ X0)
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq58
    | exact resolve eq58 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq928 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq923 X0
       have i₂ := eq13 (M.op X0 X0) X0
       grind)
    | exact superpose eq13 eq923
    | exact resolve eq923 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq930 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq917 X0
       have i₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact superpose eq13 eq917
    | exact resolve eq917 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq938 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq928 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq928
    | exact resolve eq928 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq928
  have eq940 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq930
  have eq5178 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq657 X0 X1
       grind)
    | (have i₁ := eq8 X0
       have i₂ := eq657 X0 X1
       grind)
    | exact superpose eq657 eq8
    | (have j1 := eq657 X0 X1
       grind)
    | exact resolve eq8 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq5385 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5178 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq5178
    | (have j0 := eq5178 X0 X1
       grind)
    | exact resolve eq5178 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178
  have eq6767 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq40
    | exact resolve eq40 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq7214 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6767 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq6767
    | (have j0 := eq6767 X0 X1
       grind)
    | exact resolve eq6767 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6767
  have eq88323 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5385 y x
       grind)
    | exact superpose eq5385 eq14
    | (have j1 := eq5385 y x
       grind)
    | exact resolve eq14 eq5385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5385
  have eq88422 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq7214 x y
       grind)
    | (have r₁ := eq88323
       have r₂ := eq7214 x y
       grind)
    | exact resolve eq88323 eq7214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214 eq88323
  have eq92069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq940 y
       have i₂ := eq88422
       grind)
    | exact superpose eq88422 eq940
    | exact resolve eq940 eq88422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq88422
  have eq92105 : y = (M.op x x) := by
    first
    | (have r₁ := eq92069
       have r₂ := eq14
       grind)
    | exact resolve eq92069 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92069
  have eq94879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq938 x
       have i₂ := eq92105
       grind)
    | exact superpose eq92105 eq938
    | exact resolve eq938 eq92105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938 eq92105
  have eq94915 : False := by grind
  exact eq94915

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq18
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq54 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq56 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq56 (σ X1) (σ X0)
       grind)
    | exact superpose eq56 eq13
    | (have j1 := eq56 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq56 X1 (τ X0)
       grind)
    | exact superpose eq56 eq17
    | (have j1 := eq56 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq17 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq56
  have eq87 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq59
    | exact resolve eq59 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq148
    | (have j0 := eq148 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq148 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq456 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq14
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq456
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq456
    | (have j1 := eq169 (σ x) (σ y)
       grind)
    | (have r₁ := eq456
       have r₂ := eq169 x y
       grind)
    | (have r₁ := eq456
       have r₂ := eq169 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq456
       have r₂ := eq169 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq456 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq456
  have eq524 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq523
  have eq527 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq558 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq527 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq527
    | (have j0 := eq527 X0
       grind)
    | exact resolve eq527 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq560 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq524
       grind)
    | exact superpose eq524 eq8
    | exact resolve eq8 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq593 : x = y ∨ x = y := by
    first
    | (have i₁ := eq560
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq560
    | exact resolve eq560 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq594 : x = y := by grind
  clear eq593
  have eq678 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq594
       grind)
    | exact superpose eq594 eq14
    | exact resolve eq14 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq752 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq678
       have i₂ := eq33 x
       grind)
    | exact superpose eq33 eq678
    | (have j1 := eq33 x
       grind)
    | exact resolve eq678 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq10299 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq752
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq752
    | (have j1 := eq558 (σ x)
       grind)
    | (have r₁ := eq752
       have r₂ := eq558 x
       grind)
    | exact resolve eq752 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq10301 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10299
  have eq10479 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10301
  have eq10485 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10479
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq10479
    | exact resolve eq10479 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10479
  have eq10958 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq678
       have i₂ := eq10485
       grind)
    | exact superpose eq10485 eq678
    | exact resolve eq678 eq10485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10485
  have eq10970 : x = (M.op x x) := by
    first
    | (have j1 := eq558 x
       grind)
    | (have r₁ := eq10958
       have r₂ := eq558 x
       grind)
    | exact resolve eq10958 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq10958
  have eq11266 : (M.op x x) = (k x x) := by grind
  have eq11268 : x = (k x x) := by
    first
    | (have i₁ := eq11266
       have i₂ := eq10970
       grind)
    | exact superpose eq10970 eq11266
    | exact resolve eq11266 eq10970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11266
  have eq11565 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq87 x
       have i₂ := eq11268
       grind)
    | exact superpose eq11268 eq87
    | (have j0 := eq87 x
       grind)
    | exact resolve eq87 eq11268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq11268
  have eq11576 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11565
  have eq12052 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq678
       have i₂ := eq11576
       grind)
    | exact superpose eq11576 eq678
    | exact resolve eq678 eq11576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq11576
  have eq12065 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq12052
       have i₂ := eq10970
       grind)
    | exact superpose eq10970 eq12052
    | exact resolve eq12052 eq10970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10970 eq12052
  have eq12066 : False := by grind
  exact eq12066

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_y_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq18
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq54 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq56 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq56 (σ X0) (σ X1)
       grind)
    | exact superpose eq56 eq13
    | (have j1 := eq56 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq56 X0 (τ X1)
       grind)
    | exact superpose eq56 eq17
    | (have j1 := eq56 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq17 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq56
  have eq87 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq59
    | exact resolve eq59 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq168 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq147
    | (have j0 := eq147 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq147 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq455 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq14
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq522 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq455
       have i₂ := eq168 y x
       grind)
    | exact superpose eq168 eq455
    | (have j1 := eq168 (σ x) (σ y)
       grind)
    | (have r₁ := eq455
       have r₂ := eq168 y x
       grind)
    | (have r₁ := eq455
       have r₂ := eq168 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq455
       have r₂ := eq168 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq455 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq455
  have eq523 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq522
  have eq526 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq557 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq526 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq526
    | (have j0 := eq526 X0
       grind)
    | exact resolve eq526 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq559 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq523
       grind)
    | exact superpose eq523 eq8
    | exact resolve eq8 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq592 : x = y ∨ x = y := by
    first
    | (have i₁ := eq559
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq559
    | exact resolve eq559 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq593 : x = y := by grind
  clear eq592
  have eq677 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq593
       grind)
    | exact superpose eq593 eq14
    | exact resolve eq14 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq751 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq677
       have i₂ := eq33 x
       grind)
    | exact superpose eq33 eq677
    | (have j1 := eq33 x
       grind)
    | exact resolve eq677 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq9809 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq751
       have i₂ := eq557 x
       grind)
    | exact superpose eq557 eq751
    | (have j1 := eq557 (σ x)
       grind)
    | (have r₁ := eq751
       have r₂ := eq557 x
       grind)
    | exact resolve eq751 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq9811 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9809
  have eq9938 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9811
  have eq9944 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9938
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq9938
    | exact resolve eq9938 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9938
  have eq10333 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq677
       have i₂ := eq9944
       grind)
    | exact superpose eq9944 eq677
    | exact resolve eq677 eq9944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9944
  have eq10345 : x = (M.op x x) := by
    first
    | (have j1 := eq557 x
       grind)
    | (have r₁ := eq10333
       have r₂ := eq557 x
       grind)
    | exact resolve eq10333 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq10333
  have eq10515 : (M.op x x) = (k x x) := by grind
  have eq10517 : x = (k x x) := by
    first
    | (have i₁ := eq10515
       have i₂ := eq10345
       grind)
    | exact superpose eq10345 eq10515
    | exact resolve eq10515 eq10345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10515
  have eq10811 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq87 x
       have i₂ := eq10517
       grind)
    | exact superpose eq10517 eq87
    | (have j0 := eq87 x
       grind)
    | exact resolve eq87 eq10517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq10517
  have eq10822 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq10811
  have eq11426 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq677
       have i₂ := eq10822
       grind)
    | exact superpose eq10822 eq677
    | exact resolve eq677 eq10822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq10822
  have eq11439 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11426
       have i₂ := eq10345
       grind)
    | exact superpose eq10345 eq11426
    | exact resolve eq11426 eq10345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10345 eq11426
  have eq11440 : False := by grind
  exact eq11440

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq55 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq55 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq55 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq58
  have eq68 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq62 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq62 X1 X1
       have r₂ := eq56 X1 X1
       grind)
    | exact resolve eq62 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq62
  have eq177 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq184 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq177 X0 X1
       have j1 := eq66 X0 X1
       grind)
    | (have r₁ := eq177 X0 X1
       have r₂ := eq66 X0 X1
       grind)
    | (have r₁ := eq177 X1 X1
       have r₂ := eq66 X1 X1
       grind)
    | exact resolve eq177 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq177
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq184 (σ X0) (σ X1)
       grind)
    | exact superpose eq184 eq13
    | exact resolve eq13 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq184 X0 X1
       grind)
    | exact superpose eq184 eq207
    | exact resolve eq207 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq207
  have eq1551 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq214 x y
       grind)
    | exact superpose eq214 eq14
    | (have r₁ := eq14
       have r₂ := eq214 x y
       grind)
    | exact resolve eq14 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1574 : False := by grind
  exact eq1574

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_pxx_pyx_pxy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq52 X1 X0
       grind)
    | (have r₁ := eq55 X1 X0
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq55 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | (have r₁ := eq55 X1 X1
       have r₂ := eq52 X1 X1
       grind)
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq55
  have eq60 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq59
    | (have j0 := eq59 (σ X1) (σ X0)
       grind)
    | exact resolve eq59 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq147 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq140 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq140 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq140 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq140 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq156 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq121
  have eq234 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq241 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1
       have j1 := eq156 X1 X0
       grind)
    | (have r₁ := eq234 X1 X0
       have r₂ := eq156 X0 X1
       grind)
    | exact resolve eq234 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq234
  have eq849 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq241 X0 X1
       grind)
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq10
    | (have j1 := eq241 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq241 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq241 X0 X1
       grind)
    | exact resolve eq10 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq863 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq849 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq870 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq863 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq863
    | (have j0 := eq863 X0 X1
       grind)
    | exact resolve eq863 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq871 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq870 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq913 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq871 x y
       grind)
    | exact superpose eq871 eq14
    | exact resolve eq14 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq1055 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq913
       have i₂ := eq147 y x
       grind)
    | exact superpose eq147 eq913
    | (have j1 := eq147 x y
       grind)
    | exact resolve eq913 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq1063 : (M.op x y) = (M.op y x) := by grind
  clear eq1055
  have eq1142 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq10
    | (have r₁ := eq10 x y
       have r₂ := eq1063
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq1063
       grind)
    | exact resolve eq10 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1145 : (M.op x y) = (k y x) := by grind
  clear eq1142
  have eq1307 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq913
       have i₂ := eq1145
       grind)
    | exact superpose eq1145 eq913
    | exact resolve eq913 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq1145
  have eq1308 : False := by grind
  exact eq1308
