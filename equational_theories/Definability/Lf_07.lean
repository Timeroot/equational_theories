import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | exact resolve eq175 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1172 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1346 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1346
    | (have j0 := eq1346 X0 X1
       grind)
    | exact resolve eq1346 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1877 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 (σ X0)
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq86
    | (have j0 := eq86 X1 (σ X0)
       grind)
    | (have r₁ := eq86 X0 (σ X0)
       have r₂ := eq27 X0
       grind)
    | exact resolve eq86 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1906 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1877
    | (have j0 := eq1877 X0 X1
       grind)
    | exact resolve eq1877 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq22860 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1172
       have i₂ := eq1493 x y
       grind)
    | exact superpose eq1493 eq1172
    | (have j1 := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1172 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq1493
  have eq22861 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22860
  have eq22862 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22861
  have eq22915 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq22862
       grind)
    | exact superpose eq22862 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq22862
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq22862
       grind)
    | exact resolve eq10 eq22862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22944 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1906 X0 y
       have i₂ := eq22862
       grind)
    | exact superpose eq22862 eq1906
    | (have j0 := eq1906 X0 x
       grind)
    | exact resolve eq1906 eq22862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq22862
  have eq28859 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq22915 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22915
  have eq68982 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq22944 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22944
  have eq68992 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq68982
       grind)
    | exact superpose eq68982 eq14
    | exact resolve eq14 eq68982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68982
  have eq69012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68992
       have i₂ := eq28859
       grind)
    | exact superpose eq28859 eq68992
    | exact resolve eq68992 eq28859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28859 eq68992
  have eq69036 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq69012
  have eq69037 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq69036
  have eq69039 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq69037
       grind)
    | exact superpose eq69037 eq8
    | exact resolve eq8 eq69037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69037
  have eq69379 : x = y ∨ x = y := by
    first
    | (have i₁ := eq69039
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq69039
    | exact resolve eq69039 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69039
  have eq69380 : x = y := by grind
  clear eq69379
  have eq69383 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69380
       grind)
    | exact superpose eq69380 eq14
    | exact resolve eq14 eq69380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69380
  have eq69384 : False := by grind
  exact eq69384

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq12 X1 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X1 X1 X2
       have j1 := eq39 X1 X1 X2
       grind)
    | (have r₁ := eq33 X0 X1 X2
       have r₂ := eq39 X0 X1 X2
       grind)
    | (have r₁ := eq33 X1 X0 X2
       have r₂ := eq39 X0 X1 X2
       grind)
    | (have r₁ := eq33 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq39 X0 X1 X2
       grind)
    | exact resolve eq33 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq39
  have eq100 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq101 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq102 (σ X1) (σ X0)
       grind)
    | exact superpose eq102 eq13
    | (have j1 := eq102 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq102 (τ X1) X0
       grind)
    | exact superpose eq102 eq16
    | (have j1 := eq102 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq102
  have eq456 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq188
    | exact resolve eq188 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq481 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq456
    | (have j0 := eq456 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq456 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq1475 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1567 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1475
       have i₂ := eq481 y x
       grind)
    | exact superpose eq481 eq1475
    | (have j1 := eq481 (σ x) (σ y)
       grind)
    | (have r₁ := eq1475
       have r₂ := eq481 y x
       grind)
    | (have r₁ := eq1475
       have r₂ := eq481 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1475
       have r₂ := eq481 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1475 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq1475
  have eq1568 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1567
  have eq1647 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1568
       grind)
    | exact superpose eq1568 eq8
    | exact resolve eq8 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq1691 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1647
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1647
    | exact resolve eq1647 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1692 : x = y := by grind
  clear eq1691
  have eq1766 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1692
       grind)
    | exact superpose eq1692 eq14
    | exact resolve eq14 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1767 : False := by grind
  exact eq1767

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X1
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
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X0 X0
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62
  have eq122 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq122 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq122 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq122 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq122
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq126 (σ X0) (σ X1)
       grind)
    | exact superpose eq126 eq13
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq149
    | exact resolve eq149 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq149
  have eq1447 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have r₁ := eq14
       have r₂ := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1468 : False := by grind
  exact eq1468

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq53 X0 X0
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X0 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq54 X1 X0
       grind)
    | (have r₁ := eq56 X1 X0
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62
  have eq122 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq122 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | (have r₁ := eq122 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq122 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq122
  have eq149 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq126 (σ X1) (σ X0)
       grind)
    | exact superpose eq126 eq13
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq126 X1 X0
       grind)
    | exact superpose eq126 eq149
    | exact resolve eq149 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq149
  have eq1445 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have r₁ := eq14
       have r₂ := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1466 : False := by grind
  exact eq1466

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq47 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq11
    | (have j0 := eq11 (σ X0) X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq11 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq115 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq124 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       have j1 := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq115 X0 X1
       have r₂ := eq10 (σ X0) X1
       grind)
    | exact resolve eq115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq143 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq388 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq132 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq132
    | (have j0 := eq132 X1 X1
       grind)
    | exact resolve eq132 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq451 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq388
    | (have j0 := eq388 X0 X1
       grind)
    | exact resolve eq388 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq388
  have eq463 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq451 X0 X1
       have j1 := eq143 X1 X0
       grind)
    | (have r₁ := eq451 X0 X0
       have r₂ := eq143 X0 X1
       grind)
    | exact resolve eq451 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq451
  have eq475 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq463 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq463
    | exact resolve eq463 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq463 (σ X1) X0
       grind)
    | exact superpose eq463 eq13
    | exact resolve eq13 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq885 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq484 x y
       grind)
    | exact superpose eq484 eq14
    | exact resolve eq14 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq899 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq885
       have i₂ := eq475 x y
       grind)
    | exact superpose eq475 eq885
    | exact resolve eq885 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq885
  have eq900 : False := by grind
  exact eq900

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
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
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq42 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq47 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq11
    | (have j0 := eq11 (σ X1) X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq11 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq117 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq127 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq117 X0 X1
       have r₂ := eq10 (σ X1) X1
       grind)
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq133 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq134 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq144 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq383 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq134
    | (have j0 := eq134 X0 X1
       grind)
    | exact resolve eq134 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq456 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq383 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq383
    | (have j0 := eq383 X0 X1
       grind)
    | exact resolve eq383 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq383
  have eq466 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq456 X0 X1
       have j1 := eq144 X1 X0
       grind)
    | (have r₁ := eq456 X0 X0
       have r₂ := eq144 X0 X1
       grind)
    | exact resolve eq456 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq456
  have eq476 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq466
    | exact resolve eq466 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq466 (σ X0) X1
       grind)
    | exact superpose eq466 eq13
    | exact resolve eq13 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq878 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq485 x y
       grind)
    | exact superpose eq485 eq14
    | exact resolve eq14 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq892 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq878
       have i₂ := eq476 y x
       grind)
    | exact superpose eq476 eq878
    | exact resolve eq878 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq878
  have eq893 : False := by grind
  exact eq893

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq56 X0 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq106 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq156 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq164 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       have j1 := eq106 (σ X0) X1
       grind)
    | (have r₁ := eq156 X0 (σ X0)
       have r₂ := eq106 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq156 X0 X1
       have r₂ := eq106 (σ X0) X1
       grind)
    | exact resolve eq156 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq156
  have eq168 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X1
       have j1 := eq158 X0 X1
       grind)
    | (have r₁ := eq164 X0 X1
       have r₂ := eq158 X0 X1
       grind)
    | exact resolve eq164 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq164
  have eq204 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq168
    | exact resolve eq168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq168 X0 (σ X1)
       grind)
    | exact superpose eq168 eq13
    | exact resolve eq13 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq754 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq209 x y
       grind)
    | exact superpose eq209 eq14
    | exact resolve eq14 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq778 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq754
       have i₂ := eq204 x y
       grind)
    | exact superpose eq204 eq754
    | exact resolve eq754 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq754
  have eq779 : False := by grind
  exact eq779

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq26 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq71 (σ X0) (σ X1)
       grind)
    | exact superpose eq71 eq13
    | (have j1 := eq71 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq71 X0 (τ X1)
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 X0 (τ X1)
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq71
  have eq828 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq122
    | exact resolve eq122 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq877 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq1639 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq14
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1649 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1747 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1649 (τ X0) (τ X1)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1649
    | (have j0 := eq1649 (τ X0) (τ X1)
       grind)
    | exact resolve eq1649 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1763 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1747 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1747
    | (have j0 := eq1747 X0 X1
       grind)
    | exact resolve eq1747 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq1765 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1763 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1763
    | (have j0 := eq1763 X0 X1
       grind)
    | exact resolve eq1763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1766 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1765 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1765
    | (have j0 := eq1765 X0 X1
       grind)
    | exact resolve eq1765 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765
  have eq1767 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1766
    | (have j0 := eq1766 X0 X1
       grind)
    | exact resolve eq1766 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq2721 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1639
       have i₂ := eq877 y x
       grind)
    | exact superpose eq877 eq1639
    | (have j1 := eq877 (σ y) (σ x)
       grind)
    | (have r₁ := eq1639
       have r₂ := eq877 y x
       grind)
    | exact resolve eq1639 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2722 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2721
  have eq2921 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2722
       grind)
    | exact superpose eq2722 eq14
    | exact resolve eq14 eq2722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2722
       grind)
    | exact superpose eq2722 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2722
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2722
       grind)
    | exact resolve eq11 eq2722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2923 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2922
  have eq2924 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2923
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2923
    | exact resolve eq2923 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923
  have eq15147 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (σ x) X0
       have i₂ := eq2924
       grind)
    | exact superpose eq2924 eq10
    | (have j0 := eq10 (σ x) X0
       grind)
    | (have r₁ := eq10 (σ x) x
       have r₂ := eq2924
       grind)
    | exact resolve eq10 eq2924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq15150 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15147
  have eq33403 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26 x X0
       have i₂ := eq15150 X0
       grind)
    | exact superpose eq15150 eq26
    | exact resolve eq26 eq15150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15150
  have eq58561 : (k x (τ (σ y))) = (τ (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33403 (σ y)
       have i₂ := eq2722
       grind)
    | exact superpose eq2722 eq33403
    | exact resolve eq33403 eq2722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722 eq33403
  have eq58572 : (k x (τ (σ y))) = (τ (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq58561
  have eq58577 : x = (k x (τ (σ y))) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58572
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq58572
    | exact resolve eq58572 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58572
  have eq58578 : x = (k x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58577
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq58577
    | exact resolve eq58577 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58577
  have eq58579 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1767 x y
       grind)
    | (have r₁ := eq58578
       have r₂ := eq1767 x y
       grind)
    | exact resolve eq58578 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767 eq58578
  have eq59134 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq877 y x
       have i₂ := eq58579
       grind)
    | exact superpose eq58579 eq877
    | (have j0 := eq877 y x
       grind)
    | exact resolve eq877 eq58579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq58579
  have eq59220 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq59134
  have eq59248 : x = (M.op x y) := by
    first
    | (have r₁ := eq59220
       have r₂ := eq2921
       grind)
    | exact resolve eq59220 eq2921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921 eq59220
  have eq59784 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq59248
       grind)
    | exact superpose eq59248 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq59248
       grind)
    | exact resolve eq11 eq59248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59785 : x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq59784
  have eq60352 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1649 x y
       have i₂ := eq59785
       grind)
    | exact superpose eq59785 eq1649
    | (have j0 := eq1649 x y
       grind)
    | exact resolve eq1649 eq59785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649 eq59785
  have eq60413 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq60352
  have eq61395 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60413
       grind)
    | exact superpose eq60413 eq14
    | exact resolve eq14 eq60413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60413
  have eq61400 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq61395
       have i₂ := eq59248
       grind)
    | exact superpose eq59248 eq61395
    | exact resolve eq61395 eq59248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61395
  have eq61401 : x = (M.op x x) := by grind
  clear eq61400
  have eq61968 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq61401
       grind)
    | exact superpose eq61401 eq10
    | (have j0 := eq10 x X0
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq61401
       grind)
    | exact resolve eq10 eq61401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61401
  have eq61971 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq61968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61968
  have eq62537 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1639
       have i₂ := eq61971 y
       grind)
    | exact superpose eq61971 eq1639
    | exact resolve eq1639 eq61971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639 eq61971
  have eq62656 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62537
  have eq63302 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq62656
       grind)
    | exact superpose eq62656 eq14
    | exact resolve eq14 eq62656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62656
  have eq63307 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq63302
       have i₂ := eq59248
       grind)
    | exact superpose eq59248 eq63302
    | exact resolve eq63302 eq59248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59248 eq63302
  have eq63308 : False := by grind
  exact eq63308
