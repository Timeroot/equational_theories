import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3997`: `x ◇ y = (z ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation3997 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3997 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3997.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X0 X2)) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq68 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq153 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128 y x
       grind)
    | exact superpose eq128 eq16
    | (have j1 := eq128 y x
       grind)
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq128 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq588 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq153
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq153
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq153
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq153
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq153 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq588
  have eq1890 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 (τ X1) (τ X0)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq158
    | (have j0 := eq158 (τ X1) (τ X0)
       grind)
    | exact resolve eq158 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq158
  have eq1931 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1890 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1890
    | (have j0 := eq1890 X0 X1
       grind)
    | exact resolve eq1890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890
  have eq1948 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1931 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq1931
    | (have j0 := eq1931 X0 X1
       grind)
    | exact resolve eq1931 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1961 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1948 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1948
    | (have j0 := eq1948 X0 X1
       grind)
    | exact resolve eq1948 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq1968 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1961 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1961
    | (have j0 := eq1961 X0 X1
       grind)
    | exact resolve eq1961 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq1974 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1968 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq1968
    | (have j0 := eq1968 X0 X1
       grind)
    | exact resolve eq1968 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1968
  have eq1979 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1974 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1974
    | (have j0 := eq1974 X0 X1
       grind)
    | exact resolve eq1974 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq1984 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1979 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1979
    | (have j0 := eq1979 X0 X1
       grind)
    | exact resolve eq1979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq7004 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq589
       grind)
    | exact superpose eq589 eq16
    | exact resolve eq16 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq7005 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7004
       have r₂ := eq22 x
       grind)
    | exact resolve eq7004 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq9724 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68 y (σ x)
       have i₂ := eq7005
       grind)
    | exact superpose eq7005 eq68
    | (have j0 := eq68 x (σ y)
       grind)
    | (have r₁ := eq68 y (σ x)
       have r₂ := eq7005
       grind)
    | exact resolve eq68 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq7005
  have eq9739 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq9724
  have eq9740 : (σ x) = (σ y) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq9739
  have eq9750 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9740
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9740
    | exact resolve eq9740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9740
  have eq9939 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 y
       have i₂ := eq9750
       grind)
    | exact superpose eq9750 eq9
    | exact resolve eq9 eq9750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9750
  have eq9957 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op y X0) = (M.op x X0) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9939 X0
       have i₂ := eq9 x X0 y
       grind)
    | exact superpose eq9 eq9939
    | exact resolve eq9939 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9939
  have eq11176 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op y X0) = (M.op x X0) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq9957 X0
       grind)
    | exact superpose eq9957 eq10
    | (have j1 := eq9957 X0
       grind)
    | exact resolve eq10 eq9957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9957
  have eq11272 : ∀ X0 : G, x = y ∨ (M.op y X0) = (M.op x X0) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq11176 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11176
    | (have j0 := eq11176 X0
       grind)
    | exact resolve eq11176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11176
  have eq11274 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y X0) = (M.op x X0) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq11272 X0
       grind)
    | exact superpose eq11272 eq16
    | (have j1 := eq11272 X0
       grind)
    | exact resolve eq16 eq11272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11272
  have eq11275 : ∀ X0 : G, (σ (k y x)) = (σ (M.op y y)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq11274 X0
       grind)
    | (have r₁ := eq11274 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq11274 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11274
  have eq11283 : ∀ X0 : G, (k y x) = (τ (σ (M.op y y))) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq11275 X0
       grind)
    | exact superpose eq11275 eq10
    | (have j1 := eq11275 X0
       grind)
    | exact resolve eq10 eq11275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11275
  have eq11380 : ∀ X0 : G, (k y x) = (M.op y y) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq11283 X0
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq11283
    | (have j0 := eq11283 X0
       grind)
    | exact resolve eq11283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11283
  have eq11512 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1984 y x
       have i₂ := eq11380 X0
       grind)
    | exact superpose eq11380 eq1984
    | (have j0 := eq1984 y x
       have j1 := eq11380 y
       grind)
    | (have r₁ := eq1984 y x
       have r₂ := eq11380 X0
       grind)
    | exact resolve eq1984 eq11380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984 eq11380
  have eq11515 : ∀ X0 : G, x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq11512 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11512
  have eq11632 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq11515 X0
       grind)
    | exact superpose eq11515 eq16
    | (have j1 := eq11515 y
       grind)
    | exact resolve eq16 eq11515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11515
  have eq11633 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq11632 y
       grind)
    | (have r₁ := eq11632 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq11632 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11632
  have eq11901 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j0 := eq11633 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11633
  have eq11902 : (M.op x y) = (M.op y y) := by grind
  clear eq11901
  have eq11907 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq11902
       grind)
    | exact superpose eq11902 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11902
       grind)
    | exact resolve eq13 eq11902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14859 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have j0 := eq11907 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11907
  have eq14864 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq153
       have i₂ := eq14859
       grind)
    | exact superpose eq14859 eq153
    | exact resolve eq153 eq14859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq14859
  have eq14872 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14864
  have eq14877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14872
       have i₂ := eq11902
       grind)
    | exact superpose eq11902 eq14872
    | exact resolve eq14872 eq11902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11902 eq14872
  have eq14881 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14877
       have r₂ := eq16
       grind)
    | exact resolve eq14877 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14877
  have eq15143 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14881
       grind)
    | exact superpose eq14881 eq16
    | exact resolve eq16 eq14881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14881
  have eq15149 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq15143
       have r₂ := eq22 x
       grind)
    | exact resolve eq15143 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15143
  have eq15153 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15149
       grind)
    | exact superpose eq15149 eq10
    | exact resolve eq10 eq15149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15149
  have eq15272 : x = y := by
    first
    | (have i₁ := eq15153
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15153
    | exact resolve eq15153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15153
  have eq15543 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15272
       grind)
    | exact superpose eq15272 eq16
    | exact resolve eq16 eq15272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15272
  have eq15549 : False := by grind
  exact eq15549

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq146 : ∀ X0 : G, (k (k X0 x) x) = (τ (k (k (σ X0) (σ x)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq60
    | exact resolve eq60 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq38
    | exact resolve eq38 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq179 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq178
    | exact resolve eq178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq225 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq125 (M.op sF1 sF1)
       have i₂ := eq175 sF1
       grind)
    | exact superpose eq175 eq125
    | exact resolve eq125 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq236 : (M.op x y) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq29 eq225
    | exact resolve eq225 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq334 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) x X2
       have i₂ := eq16 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 X0) X1)
       have i₂ := eq16 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq689 X0 X2
       grind)
    | (have i₁ := eq689 X0 X2
       have i₂ := eq689 X0 (M.op X0 X0)
       grind)
    | exact superpose eq689 eq689
    | exact resolve eq689 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (M.op X0 X0)
       have i₂ := eq689 X0 X1
       grind)
    | (have i₁ := eq28 X0 (M.op X0 X0)
       have i₂ := eq689 X0 (M.op X0 X0)
       grind)
    | exact superpose eq689 eq28
    | (have j0 := eq28 X2 (M.op X0 X0)
       grind)
    | exact resolve eq28 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 x (M.op X0 X0)
       have i₂ := eq689 X0 x
       grind)
    | (have i₁ := eq11 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq689 X0 x
       grind)
    | exact superpose eq689 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq11 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (k X0 (M.op X1 X1)) X2) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 (M.op (M.op X1 X1) X2)) ∨ (M.op (M.op X1 X1) X2) = (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) ∨ (M.op X0 X0) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1
       have i₂ := eq11 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq11 eq689
    | (have j1 := eq11 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq689 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq766 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq771 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq775 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq775 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq792 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq757 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq794 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq752 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq796 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq750 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq798 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq746 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq813 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 (M.op (M.op X1 X1) X2)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X2) ∨ (M.op X0 X0) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq756 X0 X1 X2
       have i₂ := eq16 X1 X2 (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq16 eq756
    | (have j0 := eq756 X0 X1 X2
       grind)
    | exact resolve eq756 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq814 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq794 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq794 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq794 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq794 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq839 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq776 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq776
    | (have j0 := eq776 (σ X0)
       grind)
    | exact resolve eq776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq814 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq814
    | (have j0 := eq814 (σ X0) X1
       grind)
    | exact resolve eq814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1726 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq766
       grind)
    | exact superpose eq766 eq40
    | exact resolve eq40 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1727 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1726
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1726
    | exact resolve eq1726 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1729 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1727
    | exact resolve eq1727 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq4716 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (M.op (σ (k X0 X0)) X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq796 (σ X1) X1 X2
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq796
    | (have j0 := eq796 (σ X0) X1 X2
       grind)
    | exact resolve eq796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4733 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (k (M.op (k X0 X0) X1) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (k X0 X0) X1)
       have i₂ := eq796 X0 X1 (M.op (k X0 X0) X1)
       grind)
    | exact superpose eq796 eq175
    | (have j1 := eq796 X0 X1 x
       grind)
    | exact resolve eq175 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4737 : ∀ X0 X1 X2 : G, (k X0 X0) = (k X1 (M.op (k X0 X0) X2)) ∨ (M.op (k X0 X0) X2) = (M.op (M.op (k X0 X0) X2) (M.op (k X0 X0) X2)) ∨ (M.op X1 X1) = (M.op (k X0 X0) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 (M.op (k X0 X0) X2)
       have i₂ := eq796 X0 X2 X1
       grind)
    | exact superpose eq796 eq11
    | (have j0 := eq11 (M.op (k X0 X0) X2) (M.op (k X0 X0) X2)
       have j1 := eq796 (M.op (k X0 X0) X2) X1 X2
       grind)
    | exact resolve eq11 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4738 : ∀ X0 X1 X2 : G, (k X0 X0) = (k X1 (M.op (k X0 X0) X2)) ∨ (k X0 X0) = (M.op (k X0 X0) X2) ∨ (M.op X1 X1) = (M.op (k X0 X0) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq796 eq4737
    | (have j0 := eq4737 X0 X1 X2
       have j1 := eq796 X0 X1 X2
       grind)
    | exact resolve eq4737 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4737
  have eq13169 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op (M.op X0 X0) X2))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X2) ∨ (M.op (M.op X0 X0) X2) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X1 (M.op (M.op X0 X0) X2)
       have i₂ := eq813 (τ X1) X0 X2
       grind)
    | exact superpose eq813 eq35
    | (have j1 := eq813 X0 X0 X2
       grind)
    | exact resolve eq35 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq813
  have eq16925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1729 eq771
    | exact resolve eq771 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16932 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16925
       have r₂ := eq27
       grind)
    | exact resolve eq16925 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16925
  have eq16939 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16932 eq218
    | exact resolve eq218 eq16932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16932
  have eq16958 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq16939
    | exact resolve eq16939 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16939
  have eq16961 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16958
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq16958
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq16958
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16958 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16958
  have eq16962 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) := by
    first
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq16961
       have r₂ := eq28 x (σ x)
       grind)
    | (have r₁ := eq16961
       have r₂ := eq28 x x
       grind)
    | exact resolve eq16961 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16961
  have eq16964 : x = (k x (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq16962 eq200
    | exact resolve eq200 eq16962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq16962
  have eq16979 : x = (k x x) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq16964
    | exact resolve eq16964 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16964
  have eq16980 : y = (k y x) := by
    first
    | (have j1 := eq814 x y
       grind)
    | (have r₁ := eq16979
       have r₂ := eq814 x x
       grind)
    | exact resolve eq16979 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16979
  have eq16984 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq766
       have i₂ := eq16980
       grind)
    | exact superpose eq16980 eq766
    | exact resolve eq766 eq16980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq16986 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq16980
       grind)
    | exact superpose eq16980 eq40
    | exact resolve eq40 eq16980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16987 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16986
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16986
    | exact resolve eq16986 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16986
  have eq16994 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16987 eq1729
    | exact resolve eq1729 eq16987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq16997 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16987 eq771
    | exact resolve eq771 eq16987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16987
  have eq17132 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16984
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq16984
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq16984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17135 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq16984
       grind)
    | exact superpose eq16984 eq16
    | exact resolve eq16 eq16984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17142 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq732 y X1 x
       have i₂ := eq16984
       grind)
    | exact superpose eq16984 eq732
    | exact resolve eq732 eq16984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17144 : ∀ X0 X1 : G, x = (M.op (k X0 x) X1) ∨ x = (M.op x x) ∨ (M.op X0 X0) = x ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq755 X0 y x
       have i₂ := eq16984
       grind)
    | exact superpose eq16984 eq755
    | exact resolve eq755 eq16984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq17146 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq16984
       grind)
    | exact superpose eq16984 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq16984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16984
  have eq17147 : x = (k y y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq17146
  have eq17148 : ∀ X0 X1 : G, x = (M.op (k X0 x) X1) ∨ x = (M.op x x) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq17144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17144
  have eq17149 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq17132
  have eq17152 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17147 eq17149
    | exact resolve eq17149 eq17147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17147 eq17149
  have eq17153 : x = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq17152
  have eq17157 : ∀ X0 X2 X3 : G, (k X0 X0) ≠ (M.op (k X0 X0) X2) ∨ (k X3 (k X0 X0)) = X3 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq740 (M.op (k X0 X0) x) x X2
       have i₂ := eq796 X0 x (M.op (k X0 X0) x)
       grind)
    | exact superpose eq796 eq740
    | (have j1 := eq796 X0 x X2
       grind)
    | (have r₁ := eq740 X0 (M.op X0 X0) X2
       have r₂ := eq796 (M.op X0 X0) x X2
       grind)
    | exact resolve eq740 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17236 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq16994
       grind)
    | exact superpose eq16994 eq16
    | exact resolve eq16 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17243 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq732 y X1 x
       have i₂ := eq16994
       grind)
    | exact superpose eq16994 eq732
    | exact resolve eq732 eq16994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16994
  have eq17282 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16997
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq16997
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq16997 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17285 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq16997 eq16
    | exact resolve eq16 eq16997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17289 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16997 eq690
    | exact resolve eq690 eq16997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq17292 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq16997 eq732
    | exact resolve eq732 eq16997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17294 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq16997 eq740
    | exact resolve eq740 eq16997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq17298 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16997 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq16997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16997
  have eq17299 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17298
  have eq17301 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17282
  have eq17302 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq17294 X0 X1
       have j1 := eq28 X1 (σ x)
       grind)
    | (have r₁ := eq17294 X0 X1
       have r₂ := eq28 X0 (σ x)
       grind)
    | exact resolve eq17294 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17294
  have eq17303 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17289 X0
       have j1 := eq28 (M.op (σ x) X0) (σ x)
       grind)
    | (have r₁ := eq17289 X0
       have r₂ := eq28 X0 (σ x)
       grind)
    | exact resolve eq17289 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17289
  have eq17305 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17299 eq17301
    | exact resolve eq17301 eq17299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17299 eq17301
  have eq17306 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17305
  have eq17312 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k (τ (M.op (σ x) X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17303 eq142
    | exact resolve eq142 eq17303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17303
  have eq17334 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq17153
       grind)
    | exact superpose eq17153 eq41
    | exact resolve eq41 eq17153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17153
  have eq17346 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17334
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17334
    | exact resolve eq17334 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17334
  have eq17352 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17346
    | exact resolve eq17346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17346
  have eq17372 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17306 eq116
    | exact resolve eq116 eq17306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17306
  have eq17387 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq17372
    | exact resolve eq17372 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17372
  have eq17429 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq17387 eq16
    | exact resolve eq16 eq17387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18042 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17135 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17135
    | (have j0 := eq17135 y X0
       grind)
    | exact resolve eq17135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18135 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq17142 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq17142 X0 y
       grind)
    | exact superpose eq17142 eq18
    | (have j1 := eq17142 y X0
       grind)
    | exact resolve eq18 eq17142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18160 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    grind
  clear eq17142
  have eq18293 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq17236 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17236
    | (have j0 := eq17236 y X0
       grind)
    | exact resolve eq17236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17236
  have eq18404 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq17243 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq17243 X0 y
       grind)
    | exact superpose eq17243 eq18
    | (have j1 := eq17243 y X0
       grind)
    | exact resolve eq18 eq17243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18435 : ∀ X0 : G, x ≠ (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    grind
  clear eq17243
  have eq18612 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq17285
    | (have j0 := eq17285 (σ y) X0
       grind)
    | exact resolve eq17285 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17285
  have eq18716 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17292 eq26
    | (have j1 := eq17292 (σ y) X0
       grind)
    | exact resolve eq26 eq17292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18745 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    grind
  clear eq17292
  have eq18819 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18716 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq18716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18820 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq18821 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18819
  have eq19156 : ∀ X0 X2 X3 : G, (M.op (σ (k X0 X0)) X2) = (M.op (σ (k X0 X0)) X3) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq732 (M.op (σ (k X0 X0)) x) x X2
       have i₂ := eq4716 X0 x (M.op (σ (k X0 X0)) x)
       grind)
    | exact superpose eq4716 eq732
    | (have j1 := eq4716 X0 x X2
       grind)
    | exact resolve eq732 eq4716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19335 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17387 eq17429
    | exact resolve eq17429 eq17387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17387 eq17429
  have eq19377 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19335
  have eq19408 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19377 eq26
    | (have j1 := eq19377 (σ y)
       grind)
    | exact resolve eq26 eq19377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19377
  have eq19464 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq19408
       grind)
    | exact superpose eq19408 eq41
    | exact resolve eq41 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19468 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq796 y X1 x
       have i₂ := eq19408
       grind)
    | exact superpose eq19408 eq796
    | (have j0 := eq796 y X1 x
       grind)
    | exact resolve eq796 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq19408
  have eq19482 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19464
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19464
    | exact resolve eq19464 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19464
  have eq19490 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19482
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19482
    | exact resolve eq19482 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19482
  have eq20157 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq18293 eq798
    | exact resolve eq798 eq18293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18293
  have eq20158 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18042 eq798
    | exact resolve eq798 eq18042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18042
  have eq20172 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18612 eq798
    | exact resolve eq798 eq18612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18612
  have eq20175 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X2) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq798 X0 X1
       grind)
    | exact superpose eq798 eq16
    | (have j1 := eq798 X0 X1
       grind)
    | exact resolve eq16 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20180 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq732 X0 X1 X2
       have i₂ := eq798 X0 X2
       grind)
    | exact superpose eq798 eq732
    | (have j1 := eq798 X0 X1
       grind)
    | exact resolve eq732 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20223 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq798 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20244 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq20172 X0
       grind)
    | (have r₁ := eq20172 X0
       have r₂ := eq18745 X0
       grind)
    | (have r₁ := eq20172 X0
       have r₂ := eq18745 (σ x)
       grind)
    | exact resolve eq20172 eq18745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18745 eq20172
  have eq20251 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20158 X0
       grind)
    | (have r₁ := eq20158 X0
       have r₂ := eq18160 X0
       grind)
    | (have r₁ := eq20158 X0
       have r₂ := eq18160 x
       grind)
    | exact resolve eq20158 eq18160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18160 eq20158
  have eq20252 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq20157 X0
       grind)
    | (have r₁ := eq20157 X0
       have r₂ := eq18435 X0
       grind)
    | (have r₁ := eq20157 X0
       have r₂ := eq18435 x
       grind)
    | exact resolve eq20157 eq18435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18435 eq20157
  have eq20280 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18716 eq20244
    | (have j0 := eq20244 (σ y)
       grind)
    | exact resolve eq20244 eq18716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18716 eq20244
  have eq20287 : (M.op x y) = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18135 eq20251
    | (have j0 := eq20251 y
       grind)
    | exact resolve eq20251 eq18135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20251
  have eq20288 : (M.op x y) = (k x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18404 eq20252
    | (have j0 := eq20252 y
       grind)
    | exact resolve eq20252 eq18404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18404 eq20252
  have eq20459 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq20287
       grind)
    | exact superpose eq20287 eq40
    | exact resolve eq40 eq20287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20287
  have eq20485 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20459
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20459
    | exact resolve eq20459 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20459
  have eq20493 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20485
    | exact resolve eq20485 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20485
  have eq20567 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq20288
       grind)
    | exact superpose eq20288 eq40
    | exact resolve eq40 eq20288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20288
  have eq20593 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20567
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20567
    | exact resolve eq20567 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20567
  have eq20601 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq20593
    | exact resolve eq20593 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20593
  have eq20642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20493 eq20280
    | exact resolve eq20280 eq20493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20661 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20642
       have r₂ := eq27
       grind)
    | exact resolve eq20642 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20642
  have eq20678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20601 eq20280
    | exact resolve eq20280 eq20601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20280 eq20601
  have eq20697 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq20678
       have r₂ := eq27
       grind)
    | exact resolve eq20678 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20678
  have eq21039 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20661 eq17312
    | exact resolve eq17312 eq20661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20661
  have eq21065 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq21039
  have eq21076 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq28 (τ (σ x)) x
       grind)
    | (have r₁ := eq21065
       have r₂ := eq28 x x
       grind)
    | exact resolve eq21065 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21065
  have eq21079 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq21076
    | exact resolve eq21076 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21076
  have eq21092 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq776 x
       have i₂ := eq21079
       grind)
    | exact superpose eq21079 eq776
    | (have j0 := eq776 x
       grind)
    | (have r₁ := eq776 x
       have r₂ := eq21079
       grind)
    | exact resolve eq776 eq21079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21098 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq839 x
       have i₂ := eq21079
       grind)
    | exact superpose eq21079 eq839
    | (have j0 := eq839 x
       grind)
    | exact resolve eq839 eq21079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21099 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq841 x X0
       have i₂ := eq21079
       grind)
    | exact superpose eq21079 eq841
    | (have j0 := eq841 x X0
       grind)
    | exact resolve eq841 eq21079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21107 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21099 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21099
  have eq21108 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21098
  have eq21110 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21092
  have eq21117 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21107 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21107
    | (have j0 := eq21107 X0
       grind)
    | exact resolve eq21107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21107
  have eq21118 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21108
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21108
    | exact resolve eq21108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21108
  have eq21310 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X1 x
       have i₂ := eq21110
       grind)
    | exact superpose eq21110 eq16
    | exact resolve eq16 eq21110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21322 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq798 x x
       have i₂ := eq21110
       grind)
    | exact superpose eq21110 eq798
    | exact resolve eq798 eq21110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21110
  have eq21335 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21079 eq21322
    | (have j0 := eq21322 X0
       grind)
    | exact resolve eq21322 eq21079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21079 eq21322
  have eq21336 : ∀ X0 : G, x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21335
  have eq21553 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq21118 eq16
    | exact resolve eq16 eq21118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21560 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq21118 eq732
    | exact resolve eq732 eq21118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21565 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21118 eq798
    | exact resolve eq798 eq21118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21118
  have eq21583 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21117 eq21565
    | (have j0 := eq21565 X0
       grind)
    | exact resolve eq21565 eq21117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21565
  have eq21584 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21583
  have eq21595 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21336 y
       grind)
    | exact superpose eq21336 eq18
    | (have j1 := eq21336 y
       grind)
    | exact resolve eq18 eq21336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21336
  have eq21670 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21584 eq26
    | (have j1 := eq21584 (σ y)
       grind)
    | exact resolve eq26 eq21584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21584
  have eq21735 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21670 eq27
    | exact resolve eq27 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21736 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq22576 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21310 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21310
    | (have j0 := eq21310 y X0
       grind)
    | exact resolve eq21310 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21310
  have eq22640 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21595 eq22576
    | exact resolve eq22576 eq21595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22576
  have eq22650 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22640 eq175
    | exact resolve eq175 eq22640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22695 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22650 eq839
    | (have j0 := eq839 (M.op x y)
       grind)
    | exact resolve eq839 eq22650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22650
  have eq22705 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22695
  have eq22713 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq22705
    | exact resolve eq22705 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22705
  have eq28987 : ∀ X0 : G, (σ (M.op x x)) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ x = (M.op (τ X0) (τ X0)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13169 x x x
       have i₂ := eq17135 x x
       grind)
    | exact superpose eq17135 eq13169
    | exact resolve eq13169 eq17135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13169 eq17135
  have eq29093 : ∀ X0 : G, (σ (M.op x x)) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28987 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28987
  have eq29174 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29093 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29093
    | (have j0 := eq29093 X0
       grind)
    | exact resolve eq29093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29093
  have eq29286 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18135 eq29174
    | (have j0 := eq29174 X0
       grind)
    | exact resolve eq29174 eq18135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18135 eq29174
  have eq29344 : ∀ X0 : G, x = (M.op (τ X0) (τ X0)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq29286
    | (have j0 := eq29286 X0
       grind)
    | exact resolve eq29286 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29286
  have eq29444 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20697 eq17312
    | exact resolve eq17312 eq20697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20697
  have eq29484 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq29444
  have eq29500 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq28 (τ (σ x)) x
       grind)
    | (have r₁ := eq29484
       have r₂ := eq28 x x
       grind)
    | exact resolve eq29484 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29484
  have eq29504 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq29500
    | exact resolve eq29500 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29500
  have eq29523 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq814 x X0
       have i₂ := eq29504
       grind)
    | exact superpose eq29504 eq814
    | (have j0 := eq814 x X0
       grind)
    | (have r₁ := eq814 x x
       have r₂ := eq29504
       grind)
    | exact resolve eq814 eq29504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29524 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq839 x
       have i₂ := eq29504
       grind)
    | exact superpose eq29504 eq839
    | (have j0 := eq839 x
       grind)
    | exact resolve eq839 eq29504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29525 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq841 x X0
       have i₂ := eq29504
       grind)
    | exact superpose eq29504 eq841
    | (have j0 := eq841 x X0
       grind)
    | exact resolve eq841 eq29504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29504
  have eq29533 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq29525 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29525
  have eq29534 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq29524
  have eq29535 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq29523 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29523
  have eq29543 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq29533 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29533
    | (have j0 := eq29533 X0
       grind)
    | exact resolve eq29533 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29533
  have eq29544 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq29534
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29534
    | exact resolve eq29534 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29534
  have eq30033 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq29544 eq798
    | exact resolve eq798 eq29544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29544
  have eq30063 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq29543 eq30033
    | (have j0 := eq30033 X0
       grind)
    | exact resolve eq30033 eq29543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29543 eq30033
  have eq30064 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq30063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30063
  have eq30167 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30064 eq26
    | (have j1 := eq30064 (σ y)
       grind)
    | exact resolve eq26 eq30064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30064
  have eq56783 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19468 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19468
    | (have j0 := eq19468 y X0
       grind)
    | exact resolve eq19468 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19468
  have eq56897 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21670 eq56783
    | (have j0 := eq56783 X0
       grind)
    | exact resolve eq56783 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56783
  have eq56943 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq56897 eq179
    | (have j1 := eq56897 X0
       grind)
    | exact resolve eq179 eq56897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq56955 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq56897 eq175
    | (have j1 := eq56897 X0
       grind)
    | exact resolve eq175 eq56897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56897
  have eq56989 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq56943
    | (have j0 := eq56943 X0
       grind)
    | exact resolve eq56943 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56943
  have eq56995 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30167 eq56989
    | (have j0 := eq56989 X0
       grind)
    | exact resolve eq56989 eq30167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56989
  have eq57000 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19490 eq56995
    | (have j0 := eq56995 X0
       grind)
    | exact resolve eq56995 eq19490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19490 eq56995
  have eq57119 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq56955 eq839
    | (have j0 := eq839 (M.op x y)
       have j1 := eq56955 X0
       grind)
    | exact resolve eq839 eq56955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56955
  have eq57138 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq57119 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57119
  have eq57157 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq57138
    | (have j0 := eq57138 X0
       grind)
    | exact resolve eq57138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57138
  have eq57172 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30167 eq57157
    | (have j0 := eq57157 X0
       grind)
    | exact resolve eq57157 eq30167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30167 eq57157
  have eq57182 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq57000 eq57172
    | (have j0 := eq57172 X0
       have j1 := eq57000 X0
       grind)
    | exact resolve eq57172 eq57000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57000 eq57172
  have eq57190 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq57182 X0
       grind)
    | (have r₁ := eq57182 X0
       have r₂ := eq18820
       grind)
    | exact resolve eq57182 eq18820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18820 eq57182
  have eq57294 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq57190 eq17312
    | (have j1 := eq57190 X0
       grind)
    | exact resolve eq17312 eq57190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57190
  have eq57359 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq57294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57294
  have eq57380 : ∀ X0 : G, x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq30 eq57359
    | (have j0 := eq57359 X0
       grind)
    | exact resolve eq57359 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57359
  have eq57611 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq814 x X0
       have i₂ := eq57380 X1
       grind)
    | exact superpose eq57380 eq814
    | (have j0 := eq814 x X0
       have j1 := eq57380 X1
       grind)
    | (have r₁ := eq814 x X1
       have r₂ := eq57380 X0
       grind)
    | exact resolve eq814 eq57380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57380
  have eq57632 : ∀ X0 X1 : G, x = (M.op (M.op x y) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq57611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57611
  have eq57691 : ∀ X0 X1 : G, (k x x) = (M.op x X0) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X1 x) = X1 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f57691_15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
      intro X0 X1
      grind
    have f57691_16 : ∀ X0 X1 : G, x = (M.op (M.op x y) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
      intro X0 X1
      grind
    have f57691_19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
      intro X0 X1
      grind
    have f57691_25 : (k x x) ≠ (M.op x X0) := by grind
    have f57691_26 : x ≠ (M.op x x) := by grind
    have f57691_27 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f57691_28 : X1 ≠ (k X1 x) := by grind
    have f57691_30 : ∀ X0 X1 : G, x = (M.op (M.op x y) X1) ∨ (k X0 x) = X0 := by
      intro X0 X1
      first
      | (have j0 := f57691_16 X0 X1
         grind)
      | (have r₁ := f57691_16 X0 X1
         have r₂ := f57691_27
         grind)
      | exact resolve f57691_16 f57691_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_75 : (M.op x X0) ≠ (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
      first
      | (have i₁ := f57691_25
         have i₂ := f57691_19 x x
         grind)
      | exact superpose f57691_19 f57691_25
      | (have j1 := f57691_19 x x
         grind)
      | exact resolve f57691_25 f57691_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_93 : (M.op x X0) ≠ (M.op x x) ∨ x = (M.op x x) := by grind
    have f57691_96 : (M.op x X0) ≠ (M.op x x) := by
      first
      | (have r₁ := f57691_93
         have r₂ := f57691_26
         grind)
      | exact resolve f57691_93 f57691_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_102 : ∀ X0 X1 : G, (k x x) = (M.op x X0) ∨ x = (M.op x x) ∨ (k X1 x) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f57691_15 (M.op x y) X1
         have i₂ := f57691_30 X0 (M.op x y)
         grind)
      | exact superpose f57691_30 f57691_15
      | (have j1 := f57691_30 X1 X1
         grind)
      | exact resolve f57691_15 f57691_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_115 : ∀ X0 X1 : G, (k x x) = (M.op x X0) ∨ (k X1 x) = X1 := by
      intro X0 X1
      first
      | (have j0 := f57691_102 X0 X1
         grind)
      | (have r₁ := f57691_102 X0 X1
         have r₂ := f57691_26
         grind)
      | exact resolve f57691_102 f57691_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_156 : ∀ X0 : G, X1 ≠ X1 ∨ (k x x) = (M.op x X0) := by
      intro X0
      first
      | (have i₁ := f57691_28
         have i₂ := f57691_115 X0 X1
         grind)
      | exact superpose f57691_115 f57691_28
      | (have j1 := f57691_115 X0 x
         grind)
      | (have r₁ := f57691_28
         have r₂ := f57691_115 X0 X1
         grind)
      | exact resolve f57691_28 f57691_115
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_160 : ∀ X0 : G, (k x x) = (M.op x X0) := by
      intro X0
      first
      | (have j0 := f57691_156 X0
         grind)
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_165 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
      intro X0 X1
      first
      | (have i₁ := f57691_160 X1
         have i₂ := f57691_160 X0
         grind)
      | exact superpose f57691_160 f57691_160
      | exact resolve f57691_160 f57691_160
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_232 : ∀ X0 : G, (M.op x x) ≠ (M.op x X0) := by
      intro X0
      first
      | (have i₁ := f57691_96
         have i₂ := f57691_165 X0 X0
         grind)
      | (have i₁ := f57691_96
         have i₂ := f57691_165 X0 X0
         grind)
      | exact superpose f57691_165 f57691_96
      | (have r₁ := f57691_96
         have r₂ := f57691_165 X0 x
         grind)
      | (have r₁ := f57691_96
         have r₂ := f57691_165 x X0
         grind)
      | exact resolve f57691_96 f57691_165
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f57691_239 : False := by
      first
      | (have r₁ := f57691_232 x
         have r₂ := f57691_165 x x
         grind)
      | (have r₁ := f57691_232 x
         have r₂ := f57691_165 x x
         grind)
      | exact resolve f57691_232 f57691_165
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f57691_239
  clear eq792 eq57632
  have eq57719 : ∀ X0 X1 : G, (k x x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57691 X0 X1
       have j1 := eq28 X1 x
       grind)
    | (have r₁ := eq57691 X0 X1
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq57691 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57691
  have eq63321 : ∀ X0 : G, (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq57719 y X0
       grind)
    | exact superpose eq57719 eq18
    | (have j1 := eq57719 y X0
       grind)
    | exact resolve eq18 eq57719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57719
  have eq63564 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 x
       have i₂ := eq63321 X0
       grind)
    | (have i₁ := eq40 X0
       have i₂ := eq63321 X0
       grind)
    | exact superpose eq63321 eq40
    | (have j1 := eq63321 X0
       grind)
    | exact resolve eq40 eq63321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63321
  have eq63625 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq63564 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq63564
    | (have j0 := eq63564 X0
       grind)
    | exact resolve eq63564 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63564
  have eq63644 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq63625
    | (have j0 := eq63625 X0
       grind)
    | exact resolve eq63625 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63625
  have eq63654 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq29535 eq63644
    | (have j0 := eq63644 X0
       have j1 := eq29535 X0
       grind)
    | exact resolve eq63644 eq29535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29535 eq63644
  have eq63687 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq18821 X0
       have i₂ := eq63654 (k X0 sF2)
       grind)
    | exact superpose eq63654 eq18821
    | (have j0 := eq18821 (σ x)
       have j1 := eq63654 X0
       grind)
    | exact resolve eq18821 eq63654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18821 eq63654
  have eq63716 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq63687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63687
  have eq63778 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq17312 X0
       have i₂ := eq63716 (M.op sF2 X0)
       grind)
    | exact superpose eq63716 eq17312
    | (have j1 := eq63716 (τ (σ x))
       grind)
    | exact resolve eq17312 eq63716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17312 eq63716
  have eq63851 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq63778 (τ (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63778
  have eq63874 : ∀ X0 : G, x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq63851
    | (have j0 := eq63851 x
       grind)
    | exact resolve eq63851 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63851
  have eq63879 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq63874 X0
       have j1 := eq814 x X0
       grind)
    | (have r₁ := eq63874 X0
       have r₂ := eq814 x x
       grind)
    | (have r₁ := eq63874 x
       have r₂ := eq814 x x
       grind)
    | exact resolve eq63874 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63874
  have eq63904 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq776 x
       have i₂ := eq63879 x
       grind)
    | exact superpose eq63879 eq776
    | (have j0 := eq776 x
       grind)
    | (have r₁ := eq776 x
       have r₂ := eq63879 x
       grind)
    | exact resolve eq776 eq63879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63910 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq839 x
       have i₂ := eq63879 x
       grind)
    | exact superpose eq63879 eq839
    | (have j0 := eq839 x
       grind)
    | exact resolve eq839 eq63879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63971 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq63879 x
       grind)
    | exact superpose eq63879 eq36
    | exact resolve eq36 eq63879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq64003 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq63910
  have eq64005 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq63904
  have eq64025 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63971
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq63971
    | exact resolve eq63971 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63971
  have eq64075 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64003
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq64003
    | exact resolve eq64003 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64003
  have eq64202 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq798 x x
       have i₂ := eq64005
       grind)
    | exact superpose eq64005 eq798
    | exact resolve eq798 eq64005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64005
  have eq64269 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq63879 eq64202
    | (have j0 := eq64202 X0
       grind)
    | exact resolve eq64202 eq63879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63879 eq64202
  have eq64270 : ∀ X0 : G, x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq64269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64269
  have eq64659 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq64075 eq798
    | exact resolve eq798 eq64075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64075
  have eq64715 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq64025 eq64659
    | (have j0 := eq64659 X0
       grind)
    | exact resolve eq64659 eq64025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64025 eq64659
  have eq64716 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq64715 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64715
  have eq64742 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq64270 y
       grind)
    | exact superpose eq64270 eq18
    | (have j1 := eq64270 y
       grind)
    | exact resolve eq18 eq64270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64270
  have eq64887 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64742 eq27
    | exact resolve eq27 eq64742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64742
  have eq64905 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64716 eq26
    | (have j1 := eq64716 (σ y)
       grind)
    | exact resolve eq26 eq64716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64716
  have eq65029 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64905
  have eq144535 : ∀ X0 : G, (k X0 x) = (k x x) ∨ x = (k x x) ∨ (M.op X0 X0) = x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4738 x x x
       have i₂ := eq17148 x x
       grind)
    | exact superpose eq17148 eq4738
    | (have j0 := eq4738 x x x
       have j1 := eq17148 X0 x
       grind)
    | exact resolve eq4738 eq17148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4738 eq17148
  have eq144580 : ∀ X0 : G, (k X0 x) = (k x x) ∨ x = (k x x) ∨ (M.op X0 X0) = x ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq144535 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144535
  have eq144632 : ∀ X0 : G, (k X0 x) = (k x x) ∨ x = (k x x) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq144580 X0
       have j1 := eq13 x x
       grind)
    | (have r₁ := eq144580 X0
       have r₂ := eq13 X0 x
       grind)
    | (have r₁ := eq144580 X0
       have r₂ := eq13 x x
       grind)
    | exact resolve eq144580 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144580
  have eq146919 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq175 (τ X0)
       have i₂ := eq29344 X0
       grind)
    | exact superpose eq29344 eq175
    | (have j1 := eq29344 X0
       grind)
    | exact resolve eq175 eq29344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29344
  have eq146983 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq146919 X0
       have j1 := eq28 (τ X0) x
       grind)
    | (have r₁ := eq146919 X0
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq146919 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146919
  have eq147062 : ∀ X0 : G, (σ (M.op x y)) = (k (σ X0) (σ x)) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f147062_14 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f147062_17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
      intro X0 X1
      grind
    have f147062_22 : ∀ X0 : G, (τ (σ X0)) = X0 := by
      intro X0
      grind
    have f147062_24 : (σ (M.op x y)) ≠ (k (σ X0) (σ x)) := by grind
    have f147062_25 : X0 ≠ (k X0 x) := by grind
    have f147062_26 : y ≠ (M.op x y) := by grind
    have f147062_28 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (σ (M.op x y)) = (k X0 (σ x)) := by
      intro X0
      first
      | (have j0 := f147062_14 X0
         grind)
      | (have r₁ := f147062_14 X0
         have r₂ := f147062_26
         grind)
      | exact resolve f147062_14 f147062_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f147062_31 : (σ (M.op x y)) ≠ (σ (k X0 x)) := by
      first
      | (have i₁ := f147062_24
         have i₂ := f147062_17 X0 x
         grind)
      | exact superpose f147062_17 f147062_24
      | exact resolve f147062_24 f147062_17
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f147062_50 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ (M.op x y)) = (k (σ X0) (σ x)) := by
      intro X0
      first
      | (have i₁ := f147062_28 (σ X0)
         have i₂ := f147062_22 X0
         grind)
      | exact superpose f147062_22 f147062_28
      | (have j0 := f147062_28 (σ X0)
         grind)
      | exact resolve f147062_28 f147062_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f147062_53 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 x)) ∨ (k X0 x) = X0 := by
      intro X0
      first
      | (have i₁ := f147062_50 X0
         have i₂ := f147062_17 X0 x
         grind)
      | exact superpose f147062_17 f147062_50
      | (have j0 := f147062_50 X0
         grind)
      | exact resolve f147062_50 f147062_17
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f147062_150 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ X0 = (k X0 x) := by
      first
      | (have i₁ := f147062_31
         have i₂ := f147062_53 X0
         grind)
      | exact superpose f147062_53 f147062_31
      | (have j1 := f147062_53 X0
         grind)
      | (have r₁ := f147062_31
         have r₂ := f147062_53 X0
         grind)
      | exact resolve f147062_31 f147062_53
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f147062_157 : X0 = (k X0 x) := by grind
    have f147062_163 : False := by
      first
      | (have r₁ := f147062_157
         have r₂ := f147062_25
         grind)
      | exact resolve f147062_157 f147062_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f147062_163
  have eq147155 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq146983
    | (have j0 := eq146983 (σ x)
       grind)
    | exact resolve eq146983 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147173 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) (σ x)) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq40 (τ X0)
       have i₂ := eq146983 X0
       grind)
    | exact superpose eq146983 eq40
    | (have j1 := eq146983 X0
       grind)
    | exact resolve eq40 eq146983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146983
  have eq147202 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq147173 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq147173
    | (have j0 := eq147173 X0
       grind)
    | exact resolve eq147173 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147173
  have eq147248 : (τ (σ (M.op x y))) = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147155 eq98
    | exact resolve eq98 eq147155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147155
  have eq147324 : (M.op x y) = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq147248
    | exact resolve eq147248 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147248
  have eq147364 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147202 eq814
    | (have j0 := eq814 (σ x) X0
       have j1 := eq147202 X0
       grind)
    | (have r₁ := eq814 (σ x) x
       have r₂ := eq147202 (σ x)
       grind)
    | exact resolve eq814 eq147202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147385 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 x) ∨ (σ X0) = (k (σ X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147202 eq60
    | (have j1 := eq147202 (σ X0)
       grind)
    | exact resolve eq60 eq147202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147530 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147202 eq98
    | (have j1 := eq147202 (σ x)
       grind)
    | exact resolve eq98 eq147202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq147202
  have eq147581 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq147530
    | exact resolve eq147530 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147530
  have eq147615 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (M.op x y) = (k X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq147385
    | (have j0 := eq147385 X0
       grind)
    | exact resolve eq147385 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147385
  have eq147625 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq147364 X0
       have j1 := eq814 (σ x) X0
       grind)
    | (have r₁ := eq147364 (σ x)
       have r₂ := eq814 (σ x) x
       grind)
    | (have r₁ := eq147364 X0
       have r₂ := eq814 (σ x) x
       grind)
    | exact resolve eq147364 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq147364
  have eq150645 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147581 eq776
    | (have j0 := eq776 (σ x)
       grind)
    | (have r₁ := eq776 (σ x)
       have r₂ := eq147581
       grind)
    | exact resolve eq776 eq147581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150672 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq150645
  have eq151026 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq150672 eq798
    | exact resolve eq798 eq150672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150672
  have eq151060 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147581 eq151026
    | (have j0 := eq151026 X0
       grind)
    | exact resolve eq151026 eq147581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147581 eq151026
  have eq151061 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq151060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151060
  have eq151359 : (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151061 eq26
    | (have j1 := eq151061 (σ y)
       grind)
    | exact resolve eq26 eq151061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151061
  have eq151517 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq151359
       grind)
    | exact superpose eq151359 eq40
    | exact resolve eq40 eq151359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151579 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq151517
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq151517
    | exact resolve eq151517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151517
  have eq151590 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq151579
    | exact resolve eq151579 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151579
  have eq152237 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 x) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147062 eq60
    | (have j1 := eq147062 X0
       grind)
    | exact resolve eq60 eq147062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147062
  have eq152306 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq152237
    | (have j0 := eq152237 X0
       grind)
    | exact resolve eq152237 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152237
  have eq152543 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq152306 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152306
  have eq156534 : ∀ X0 : G, (τ (k (σ X0) (σ x))) = (k (k X0 x) x) ∨ (M.op x y) = (k X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq147615 eq146
    | (have j1 := eq147615 X0
       grind)
    | exact resolve eq146 eq147615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq147615
  have eq156599 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) ∨ (M.op x y) = (k X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq60 eq156534
    | (have j0 := eq156534 X0
       grind)
    | exact resolve eq156534 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq156534
  have eq156617 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq156599 X0
       have j1 := eq152543 (k X0 x)
       grind)
    | (have r₁ := eq156599 X0
       have r₂ := eq152543 (k X0 x)
       grind)
    | (have r₁ := eq156599 X0
       have r₂ := eq152543 y
       grind)
    | exact resolve eq156599 eq152543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152543 eq156599
  have eq156747 : ∀ X0 : G, (σ (k (τ X0) x)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq334 X0 x x
       have i₂ := eq156617 (τ X0)
       grind)
    | exact superpose eq156617 eq334
    | exact resolve eq334 eq156617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq156617
  have eq156801 : ∀ X0 : G, (σ (k (τ X0) x)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq156747 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq156747
    | (have j0 := eq156747 X0
       grind)
    | exact resolve eq156747 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156747
  have eq156813 : ∀ X0 : G, (k (σ (τ X0)) (σ x)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq156801 X0
       have i₂ := eq40 (τ X0)
       grind)
    | exact superpose eq40 eq156801
    | exact resolve eq156801 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq156801
  have eq156820 : ∀ X0 : G, (k X0 (σ x)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq156813 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq156813
    | exact resolve eq156813 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156813
  have eq156898 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq771 eq156820
    | exact resolve eq156820 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq156820
  have eq156954 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq28 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq156898
       have r₂ := eq28 x (σ x)
       grind)
    | exact resolve eq156898 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156898
  have eq240912 : y = (k x x) ∨ x = (k x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16980
       have i₂ := eq144632 y
       grind)
    | exact superpose eq144632 eq16980
    | (have j1 := eq144632 y
       grind)
    | exact resolve eq16980 eq144632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16980 eq144632
  have eq241307 : y = (M.op x y) ∨ x = (k x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147324 eq240912
    | exact resolve eq240912 eq147324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147324 eq240912
  have eq241308 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq241307
  have eq241771 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq151359
       have i₂ := eq241308
       grind)
    | exact superpose eq241308 eq151359
    | exact resolve eq151359 eq241308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151359
  have eq241809 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq839 x
       have i₂ := eq241308
       grind)
    | exact superpose eq241308 eq839
    | (have j0 := eq839 x
       grind)
    | exact resolve eq839 eq241308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241810 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq841 x X0
       have i₂ := eq241308
       grind)
    | exact superpose eq241308 eq841
    | (have j0 := eq841 x X0
       grind)
    | exact resolve eq841 eq241308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq241308
  have eq241833 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq241810 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241810
  have eq241834 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq241809
  have eq241857 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq241771
  have eq241884 : ∀ X0 : G, x = (M.op y y) ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq241833 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq241833
    | (have j0 := eq241833 X0
       grind)
    | exact resolve eq241833 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241833
  have eq241885 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq241834
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq241834
    | exact resolve eq241834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241834
  have eq241903 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21595 eq241857
    | exact resolve eq241857 eq21595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241857
  have eq241988 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) ∨ (k X2 (σ x)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq732 y X1 X2
       have i₂ := eq241884 X0
       grind)
    | exact superpose eq241884 eq732
    | (have j1 := eq241884 X2
       grind)
    | exact resolve eq732 eq241884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242006 : ∀ X0 : G, x = (k y y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 y y
       have i₂ := eq241884 X0
       grind)
    | exact superpose eq241884 eq11
    | (have j1 := eq241884 X0
       grind)
    | exact resolve eq11 eq241884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242007 : ∀ X0 : G, x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq242006 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242006
  have eq242142 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq241885 eq798
    | exact resolve eq798 eq241885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241885
  have eq242195 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq241884 eq242142
    | (have j0 := eq242142 X0
       grind)
    | exact resolve eq242142 eq241884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241884 eq242142
  have eq242196 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq242195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242195
  have eq242467 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq242196 eq26
    | (have j1 := eq242196 (σ y)
       grind)
    | exact resolve eq26 eq242196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242196
  have eq242625 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq242467
       grind)
    | exact superpose eq242467 eq16
    | exact resolve eq16 eq242467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242632 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq732 y X1 x
       have i₂ := eq242467
       grind)
    | exact superpose eq242467 eq732
    | exact resolve eq732 eq242467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242650 : x = (k y y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq242467
       grind)
    | exact superpose eq242467 eq11
    | exact resolve eq11 eq242467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242467
  have eq242651 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq242650
  have eq242684 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq242625 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq242625
    | (have j0 := eq242625 y X0
       grind)
    | exact resolve eq242625 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242625
  have eq243237 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq242632 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq242632 X0 y
       grind)
    | exact superpose eq242632 eq18
    | (have j1 := eq242632 y X0
       grind)
    | exact resolve eq18 eq242632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242632
  have eq243863 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq798 x x
       have i₂ := eq243237 x
       grind)
    | exact superpose eq243237 eq798
    | exact resolve eq798 eq243237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243237
  have eq243956 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq22640 eq243863
    | (have j0 := eq243863 X0
       have j1 := eq22640 X0
       grind)
    | exact resolve eq243863 eq22640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243863
  have eq245332 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq242651
       grind)
    | exact superpose eq242651 eq41
    | exact resolve eq41 eq242651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242651
  have eq245368 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq245332
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq245332
    | exact resolve eq245332 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245332
  have eq245378 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq245368
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq245368
    | exact resolve eq245368 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245368
  have eq245630 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq241903
       grind)
    | exact superpose eq241903 eq16
    | exact resolve eq16 eq241903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241903
  have eq248705 : ∀ X0 X1 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18
       have i₂ := eq241988 y X0 X1
       grind)
    | (have i₁ := eq18
       have i₂ := eq241988 X0 y X1
       grind)
    | exact superpose eq241988 eq18
    | (have j1 := eq241988 y X0 X1
       grind)
    | exact resolve eq18 eq241988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241988
  have eq252318 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq839 y
       have i₂ := eq242007 X0
       grind)
    | exact superpose eq242007 eq839
    | (have j0 := eq839 y
       have j1 := eq242007 X0
       grind)
    | exact resolve eq839 eq242007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq242007
  have eq252345 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq252318 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq252318
    | (have j0 := eq252318 X0
       grind)
    | exact resolve eq252318 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252318
  have eq252355 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq252345 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq252345
    | (have j0 := eq252345 X0
       grind)
    | exact resolve eq252345 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252345
  have eq252362 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq252355 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq252355
    | (have j0 := eq252355 X0
       grind)
    | exact resolve eq252355 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252355
  have eq252618 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq17352 eq17157
    | (have j0 := eq17157 (σ y) x x
       grind)
    | exact resolve eq17157 eq17352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17352
  have eq252626 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq245378 eq17157
    | (have j0 := eq17157 (σ y) x x
       grind)
    | exact resolve eq17157 eq245378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17157 eq245378
  have eq252670 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq17302 eq252626
    | (have j0 := eq252626 X0 X1
       have j1 := eq17302 X0 X1
       grind)
    | (have r₁ := eq252626 X0 X1
       have r₂ := eq17302 (σ y) X1
       grind)
    | exact resolve eq252626 eq17302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17302 eq252626
  have eq252673 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq248705 eq252618
    | (have j0 := eq252618 X0 X1
       have j1 := eq248705 X0 X1
       grind)
    | exact resolve eq252618 eq248705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248705 eq252618
  have eq252710 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq252670 X0 X1
       have j1 := eq252362 X1
       grind)
    | (have r₁ := eq252670 X0 X1
       have r₂ := eq252362 X0
       grind)
    | exact resolve eq252670 eq252362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252362 eq252670
  have eq252721 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq252673 eq252710
    | (have j0 := eq252710 X0 X1
       have j1 := eq252673 X0 X1
       grind)
    | exact resolve eq252710 eq252673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252673 eq252710
  have eq252722 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq252721 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252721
  have eq257901 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq245630 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq245630
    | (have j0 := eq245630 y X0
       grind)
    | exact resolve eq245630 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245630
  have eq280620 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq257901 eq243956
    | exact resolve eq243956 eq257901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257901
  have eq280670 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq243956 eq242684
    | (have j1 := eq243956 X0
       grind)
    | exact resolve eq242684 eq243956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242684 eq243956
  have eq280740 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq280670 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280670
  have eq280760 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq280620
  have eq280781 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq280740 X0
       grind)
    | (have r₁ := eq280740 X0
       have r₂ := eq21736
       grind)
    | exact resolve eq280740 eq21736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21736 eq280740
  have eq280813 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22640 eq280781
    | (have j0 := eq280781 X0
       have j1 := eq22640 X0
       grind)
    | exact resolve eq280781 eq22640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22640 eq280781
  have eq281151 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq280813 eq175
    | exact resolve eq175 eq280813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280813
  have eq281509 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq281151
  have eq281565 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq281509
       have r₂ := eq280760
       grind)
    | exact resolve eq281509 eq280760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280760 eq281509
  have eq281627 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq281565 eq42
    | exact resolve eq42 eq281565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq281645 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq281565 eq4716
    | (have j0 := eq4716 (M.op x y) X1 x
       grind)
    | exact resolve eq4716 eq281565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281655 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq281565 eq19156
    | (have j0 := eq19156 (M.op x y) x x
       grind)
    | exact resolve eq19156 eq281565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281687 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq281655 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq281655
    | (have j0 := eq281655 X0 X1
       grind)
    | exact resolve eq281655 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281655
  have eq281689 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq281645 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq281645
    | (have j0 := eq281645 X0 X1
       grind)
    | exact resolve eq281645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281645
  have eq281695 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq281627
    | exact resolve eq281627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281627
  have eq281703 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq20 eq281687
    | (have j0 := eq281687 X0 X1
       grind)
    | exact resolve eq281687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281687
  have eq281705 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq20 eq281689
    | (have j0 := eq281689 X0 X1
       grind)
    | exact resolve eq281689 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281689
  have eq281710 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq281695
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq281695
    | exact resolve eq281695 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281695
  have eq286433 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq252722
    | (have j0 := eq252722 (σ y) X0
       grind)
    | exact resolve eq252722 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286577 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21117 eq286433
    | (have j0 := eq286433 X0
       have j1 := eq21117 X0
       grind)
    | exact resolve eq286433 eq21117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21117 eq286433
  have eq297231 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq281703 eq26
    | (have j1 := eq281703 (σ y) X0
       grind)
    | exact resolve eq26 eq281703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281703
  have eq297551 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22713 eq297231
    | exact resolve eq297231 eq22713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22713 eq297231
  have eq297857 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq297551 eq16
    | exact resolve eq16 eq297551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297864 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq297551 eq732
    | exact resolve eq732 eq297551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297883 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq297551 eq20180
    | exact resolve eq20180 eq297551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298367 : ∀ X1 : G, (σ x) = (M.op (σ y) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq297551 eq281705
    | exact resolve eq281705 eq297551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281705 eq297551
  have eq298430 : ∀ X1 : G, (σ x) = (M.op (σ y) X1) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq298367 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298367
  have eq303587 : (σ y) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq297857 eq798
    | exact resolve eq798 eq297857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303644 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq297883 eq303587
    | (have j1 := eq297883 x (σ y)
       grind)
    | exact resolve eq303587 eq297883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303587
  have eq303660 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq298430 eq303644
    | exact resolve eq303644 eq298430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303644
  have eq303661 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq303660
  have eq303823 : ∀ X0 X1 X2 : G, (M.op (σ y) X0) = (M.op (k (M.op (σ y) X0) (M.op (σ y) X0)) X1) ∨ (M.op (σ y) X0) = (M.op (M.op (σ y) X0) X2) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq297864 eq20175
    | exact resolve eq20175 eq297864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20175 eq297864
  have eq303844 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (k (M.op (σ y) X0) (M.op (σ y) X0)) X1) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq297857 eq303823
    | (have j0 := eq303823 X0 X1 x
       grind)
    | exact resolve eq303823 eq297857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297857 eq303823
  have eq303904 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (M.op (k (k (σ y) (σ y)) (k (σ y) (σ y))) X1) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq297883 eq303844
    | (have j0 := eq303844 X0 X1
       have j1 := eq297883 X0 X0
       grind)
    | exact resolve eq303844 eq297883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297883 eq303844
  have eq303944 : ∀ X1 : G, (k (σ y) (σ y)) = (M.op (k (k (σ y) (σ y)) (k (σ y) (σ y))) X1) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq298430 eq303904
    | (have j0 := eq303904 x X1
       grind)
    | exact resolve eq303904 eq298430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303904
  have eq303945 : ∀ X1 : G, (k (σ y) (σ y)) = (M.op (k (k (σ y) (σ y)) (k (σ y) (σ y))) X1) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq303944 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303944
  have eq303978 : ∀ X1 : G, (k (σ y) (σ y)) = (M.op (σ y) X1) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq303661 eq303945
    | exact resolve eq303945 eq303661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303661 eq303945
  have eq304001 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq298430 eq303978
    | exact resolve eq303978 eq298430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298430 eq303978
  have eq304082 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq304001 eq116
    | exact resolve eq116 eq304001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304001
  have eq304131 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq304082
    | exact resolve eq304082 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304082
  have eq304146 : (M.op x y) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq304131 eq236
    | exact resolve eq236 eq304131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq304175 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq304131 eq16
    | exact resolve eq16 eq304131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304176 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq304131 eq28
    | (have j0 := eq28 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq28 X0 (σ (M.op x y))
       have r₂ := eq304131
       grind)
    | exact resolve eq28 eq304131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304177 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq304131 eq175
    | exact resolve eq175 eq304131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304205 : ∀ X0 : G, x = (k y y) ∨ (σ x) = (σ y) ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq304176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304176
  have eq304236 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq281710 eq304177
    | exact resolve eq304177 eq281710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281710 eq304177
  have eq304239 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq304146
    | exact resolve eq304146 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq304146
  have eq304245 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq281565 eq304239
    | exact resolve eq304239 eq281565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281565 eq304239
  have eq304269 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq304236
       grind)
    | exact superpose eq304236 eq41
    | exact resolve eq41 eq304236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304309 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq304269
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq304269
    | exact resolve eq304269 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304269
  have eq304320 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq304309
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq304309
    | exact resolve eq304309 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304309
  have eq304340 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq304245
       grind)
    | exact superpose eq304245 eq41
    | exact resolve eq41 eq304245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304245
  have eq304381 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq304340
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq304340
    | exact resolve eq304340 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304340
  have eq304393 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq304381
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq304381
    | exact resolve eq304381 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304381
  have eq304428 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq304320 eq4733
    | (have j0 := eq4733 (σ y) x
       grind)
    | exact resolve eq4733 eq304320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733
  have eq304443 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq304428 X0
       have j1 := eq286577 (M.op (σ x) X0)
       grind)
    | (have r₁ := eq304428 X0
       have r₂ := eq286577 X0
       grind)
    | exact resolve eq304428 eq286577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304428
  have eq304453 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq304443 X0
       have j1 := eq147625 (M.op (σ x) X0)
       grind)
    | (have r₁ := eq304443 X0
       have r₂ := eq147625 X0
       grind)
    | exact resolve eq304443 eq147625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147625 eq304443
  have eq304528 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq41 y
       have i₂ := eq304205 X0
       grind)
    | exact superpose eq304205 eq41
    | (have j1 := eq304205 X0
       grind)
    | exact resolve eq41 eq304205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304205
  have eq304570 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq304528 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq304528
    | (have j0 := eq304528 X0
       grind)
    | exact resolve eq304528 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304528
  have eq304581 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq304570 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq304570
    | (have j0 := eq304570 X0
       grind)
    | exact resolve eq304570 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304570
  have eq304590 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq304320 eq304581
    | exact resolve eq304581 eq304320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304320 eq304581
  have eq304599 : ∀ X0 : G, (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq116
       have i₂ := eq304590 (k sF3 sF3)
       grind)
    | exact superpose eq304590 eq116
    | (have j1 := eq304590 X0
       grind)
    | exact resolve eq116 eq304590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq304590
  have eq304652 : ∀ X0 : G, x = (k y y) ∨ (σ x) = (σ y) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq304599
    | (have j0 := eq304599 X0
       grind)
    | exact resolve eq304599 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304599
  have eq304729 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq304453
    | (have j0 := eq304453 (σ y)
       grind)
    | exact resolve eq304453 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304847 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq156954 eq304729
    | exact resolve eq304729 eq156954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156954 eq304729
  have eq327125 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq304131 eq304175
    | exact resolve eq304175 eq304131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304131 eq304175
  have eq327218 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq327125 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327125
  have eq327239 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq304236 eq327218
    | exact resolve eq327218 eq304236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304236 eq327218
  have eq327294 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq327239 eq26
    | (have j1 := eq327239 (σ y)
       grind)
    | exact resolve eq26 eq327239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327388 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq327239 eq304453
    | exact resolve eq304453 eq327239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327239
  have eq327430 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k y y) := by grind
  clear eq327388
  have eq327503 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have j1 := eq286577 (σ x)
       grind)
    | (have r₁ := eq327430
       have r₂ := eq286577 x
       grind)
    | exact resolve eq327430 eq286577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327430
  have eq327511 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq327294
       have r₂ := eq65029
       grind)
    | exact resolve eq327294 eq65029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327294
  have eq327515 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq304652 eq327503
    | (have j1 := eq304652 (σ x)
       grind)
    | exact resolve eq327503 eq304652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304652 eq327503
  have eq327518 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq327515
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq327515 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327515
  have eq327536 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq327511
       grind)
    | exact superpose eq327511 eq41
    | exact resolve eq41 eq327511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq327550 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq4716 y X1 x
       have i₂ := eq327511
       grind)
    | exact superpose eq327511 eq4716
    | (have j0 := eq4716 y X1 x
       grind)
    | exact resolve eq4716 eq327511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4716
  have eq327560 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19156 y x x
       have i₂ := eq327511
       grind)
    | exact superpose eq327511 eq19156
    | (have j0 := eq19156 y x x
       grind)
    | exact resolve eq19156 eq327511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19156 eq327511
  have eq327568 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq327560 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq327560
    | (have j0 := eq327560 X0 X1
       grind)
    | exact resolve eq327560 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327560
  have eq327571 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq327550 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq327550
    | (have j0 := eq327550 X0 X1
       grind)
    | exact resolve eq327550 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327550
  have eq327577 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq327536
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq327536
    | exact resolve eq327536 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327536
  have eq327581 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq327568 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq327568
    | (have j0 := eq327568 X0 X1
       grind)
    | exact resolve eq327568 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327568
  have eq327583 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq327571 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq327571
    | (have j0 := eq327571 X0 X1
       grind)
    | exact resolve eq327571 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327571
  have eq327588 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq327577
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq327577
    | exact resolve eq327577 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327577
  have eq327590 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq21560 eq327581
    | (have j0 := eq327581 X0 X1
       have j1 := eq21560 X0 X1
       grind)
    | exact resolve eq327581 eq21560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21560 eq327581
  have eq327592 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq21553 eq327583
    | (have j0 := eq327583 X0 X1
       have j1 := eq21553 X0 X1
       grind)
    | exact resolve eq327583 eq21553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21553 eq327583
  have eq327809 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq327518 eq776
    | (have j0 := eq776 (σ x)
       grind)
    | (have r₁ := eq776 (σ x)
       have r₂ := eq327518
       grind)
    | exact resolve eq776 eq327518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq327518
  have eq327843 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq327809
  have eq328089 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ y = (M.op x y) ∨ x = (k y y) := by
    intro X0 X1
    first
    | exact superpose eq327843 eq16
    | exact resolve eq16 eq327843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328096 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) ∨ x = (k y y) := by
    intro X0 X1
    first
    | exact superpose eq327843 eq732
    | exact resolve eq732 eq327843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327843
  have eq342768 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq327590 eq26
    | (have j1 := eq327590 (σ y) X0
       grind)
    | exact resolve eq26 eq327590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327590
  have eq343553 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq342768 eq304453
    | (have j0 := eq304453 (σ y)
       grind)
    | exact resolve eq304453 eq342768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304453
  have eq343614 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq343553
  have eq343727 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq286577 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq343614
       have r₂ := eq286577 x
       grind)
    | exact resolve eq343614 eq286577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343614
  have eq343829 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq304847 eq343727
    | exact resolve eq343727 eq304847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304847 eq343727
  have eq343837 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq28 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq343829
       have r₂ := eq28 x (σ x)
       grind)
    | exact resolve eq343829 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343829
  have eq343853 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq343837 eq142
    | exact resolve eq142 eq343837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq343837
  have eq348535 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq342768 eq327592
    | (have j0 := eq327592 (σ y) X1
       grind)
    | exact resolve eq327592 eq342768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327592 eq342768
  have eq348598 : ∀ X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq348535 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348535
  have eq348718 : ∀ X0 : G, y = (k y (τ (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq348598 eq218
    | (have j1 := eq348598 X0
       grind)
    | exact resolve eq218 eq348598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq348745 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq348598 eq175
    | (have j1 := eq348598 X0
       grind)
    | exact resolve eq175 eq348598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq348598
  have eq348800 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32 eq348718
    | (have j0 := eq348718 X0
       grind)
    | exact resolve eq348718 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq348718
  have eq348886 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq348745 eq304393
    | (have j1 := eq348745 X0
       grind)
    | exact resolve eq304393 eq348745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304393 eq348745
  have eq348939 : ∀ X0 : G, (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq348886 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348886
  have eq349000 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21595 eq348939
    | exact resolve eq348939 eq21595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21595 eq348939
  have eq351071 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq349000 eq16
    | exact resolve eq16 eq349000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351078 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq349000 eq732
    | exact resolve eq732 eq349000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349000
  have eq351893 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq348800 eq16
    | exact resolve eq16 eq348800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351900 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq348800 eq732
    | exact resolve eq732 eq348800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq348800
  have eq351936 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq328096 eq351900
    | (have j0 := eq351900 X0 X1
       have j1 := eq328096 X0 X1
       grind)
    | exact resolve eq351900 eq328096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328096 eq351900
  have eq351940 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq328089 eq351893
    | (have j0 := eq351893 X0 X1
       have j1 := eq328089 X0 X1
       grind)
    | exact resolve eq351893 eq328089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328089 eq351893
  have eq351952 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq351078 eq351936
    | (have j0 := eq351936 X0 X1
       have j1 := eq351078 X0 X1
       grind)
    | exact resolve eq351936 eq351078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351078 eq351936
  have eq351953 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq351952 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351952
  have eq351960 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq351071 eq351940
    | (have j0 := eq351940 X0 X1
       have j1 := eq351071 X0 X1
       grind)
    | exact resolve eq351940 eq351071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351071 eq351940
  have eq351961 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq351960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351960
  have eq352592 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq351953 eq26
    | (have j1 := eq351953 (σ y) X0
       grind)
    | exact resolve eq26 eq351953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq351953
  have eq356796 : ∀ X1 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X1
    first
    | exact superpose eq352592 eq252722
    | (have j0 := eq252722 (σ y) X1
       grind)
    | exact resolve eq252722 eq352592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252722
  have eq356830 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq352592 eq16
    | exact resolve eq16 eq352592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356831 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq352592 eq28
    | (have j0 := eq28 X0 (σ x)
       grind)
    | exact resolve eq28 eq352592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356856 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X1) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq352592 eq20180
    | exact resolve eq20180 eq352592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20180
  have eq356893 : ∀ X1 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have j0 := eq356796 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356796
  have eq356997 : ∀ X1 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq356893 X1
       have j1 := eq286577 X1
       grind)
    | (have r₁ := eq356893 X1
       have r₂ := eq286577 x
       grind)
    | exact resolve eq356893 eq286577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286577 eq356893
  have eq357095 : ∀ X1 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq356831 eq356997
    | (have j0 := eq356997 X1
       have j1 := eq356831 X1
       grind)
    | exact resolve eq356997 eq356831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356831 eq356997
  have eq357102 : ∀ X1 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X1 (σ x)) = X1 ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq357095 X1
       have j1 := eq28 X1 (σ x)
       grind)
    | (have r₁ := eq357095 X1
       have r₂ := eq28 x (σ x)
       grind)
    | exact resolve eq357095 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq357095
  have eq357210 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X1
    first
    | exact superpose eq352592 eq351961
    | (have j0 := eq351961 (σ y) X1
       grind)
    | exact resolve eq351961 eq352592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351961 eq352592
  have eq357273 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have j0 := eq357210 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357210
  have eq357475 : (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq356830 eq798
    | exact resolve eq798 eq356830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq356830
  have eq357537 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq356856 eq357475
    | (have j1 := eq356856 x (M.op (σ x) (σ y))
       grind)
    | exact resolve eq357475 eq356856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356856 eq357475
  have eq357563 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq357273 eq357537
    | exact resolve eq357537 eq357273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357273 eq357537
  have eq357581 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq357563
       have r₂ := eq65029
       grind)
    | exact resolve eq357563 eq65029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357563
  have eq357591 : (σ y) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21670 eq357581
    | exact resolve eq357581 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21670 eq357581
  have eq357600 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq327588 eq357591
    | exact resolve eq357591 eq327588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327588 eq357591
  have eq357684 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq357600 eq151590
    | exact resolve eq151590 eq357600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151590 eq357600
  have eq357796 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq357684
  have eq357873 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq357796
       have r₂ := eq21735
       grind)
    | exact resolve eq357796 eq21735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21735 eq357796
  have eq357954 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq357873 eq27
    | exact resolve eq27 eq357873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357993 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq357873 eq343853
    | exact resolve eq343853 eq357873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343853
  have eq358005 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq357873 eq357102
    | (have j0 := eq357102 X0
       grind)
    | (have r₁ := eq357102 x
       have r₂ := eq357873
       grind)
    | exact resolve eq357102 eq357873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357102 eq357873
  have eq358008 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq358005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358005
  have eq358009 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq358008 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358008
  have eq358021 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) := by grind
  clear eq357993
  have eq358043 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq358021
    | exact resolve eq358021 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq358021
  have eq358391 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq358009 eq20493
    | exact resolve eq20493 eq358009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20493 eq358009
  have eq358459 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq358391
  have eq358635 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq358459
       have r₂ := eq357954
       grind)
    | exact resolve eq358459 eq357954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358459
  have eq360393 : ∀ X0 : G, x ≠ (k x x) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20223 x x
       have i₂ := eq358635
       grind)
    | exact superpose eq358635 eq20223
    | exact resolve eq20223 eq358635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20223 eq358635
  have eq360511 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq360393 X0
       grind)
    | (have r₁ := eq360393 X0
       have r₂ := eq358043
       grind)
    | exact resolve eq360393 eq358043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358043 eq360393
  have eq360912 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq360511 y
       grind)
    | exact superpose eq360511 eq18
    | (have j1 := eq360511 y
       grind)
    | exact resolve eq18 eq360511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq360511
  have eq361235 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq360912
       grind)
    | exact superpose eq360912 eq24
    | exact resolve eq24 eq360912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360912
  have eq361377 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq361235
    | exact resolve eq361235 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361235
  have eq361384 : x = (M.op x y) := by
    first
    | (have r₁ := eq361377
       have r₂ := eq64887
       grind)
    | exact resolve eq361377 eq64887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64887 eq361377
  have eq361388 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq361384
       grind)
    | exact superpose eq361384 eq22
    | exact resolve eq22 eq361384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq361384
  have eq362149 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq361388 eq20
    | exact resolve eq20 eq361388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq363568 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq362149 eq357954
    | (have r₁ := eq357954
       have r₂ := eq362149
       grind)
    | exact resolve eq357954 eq362149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357954
  have eq363569 : y = (M.op x y) := by grind
  clear eq363568
  have eq363824 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq363569
       grind)
    | exact superpose eq363569 eq24
    | exact resolve eq24 eq363569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq363569
  have eq363971 : (σ x) = (σ y) := by
    first
    | exact superpose eq361388 eq363824
    | exact resolve eq363824 eq361388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361388 eq363824
  have eq364167 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq363971 eq65029
    | (have r₁ := eq65029
       have r₂ := eq363971
       grind)
    | exact resolve eq65029 eq363971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65029 eq363971
  have eq364250 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq364167
  have eq364560 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq364250 eq27
    | exact resolve eq27 eq364250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq364250
  have eq364621 : False := by grind
  exact eq364621

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_x_x_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq84 X0 X0
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq84 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq84 X1 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq197 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq204 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq206 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq204 X0 (σ X0)
       have r₂ := eq13 X0 (σ X0)
       grind)
    | (have r₁ := eq204 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq204 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq209 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq206 X0 X0
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq206 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq214 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq209 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq209
    | (have j0 := eq209 (τ X0) X1
       grind)
    | exact resolve eq209 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq216 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214
    | (have j0 := eq214 X0 X1
       grind)
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq219 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq216
    | (have j0 := eq216 X0 X1
       grind)
    | exact resolve eq216 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq225 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq219 (τ X0) X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq219
    | (have j0 := eq219 (τ X0) X1
       grind)
    | exact resolve eq219 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq328 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq197 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq197
    | (have j0 := eq197 (τ X0)
       grind)
    | exact resolve eq197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq330 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq328 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq328
    | (have j0 := eq328 X0
       grind)
    | exact resolve eq328 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq333 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq330 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq330
    | (have j0 := eq330 X0
       grind)
    | exact resolve eq330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq353 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq333 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq333
    | (have j0 := eq333 (τ X0)
       grind)
    | exact resolve eq333 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq753 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq196 (τ X1) (τ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq196
    | (have j0 := eq196 (τ X1) (τ X1)
       grind)
    | exact resolve eq196 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq753
    | (have j0 := eq753 X1 X1
       grind)
    | exact resolve eq753 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq765 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq762
    | (have j0 := eq762 X1 X1
       grind)
    | exact resolve eq762 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq766 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq765 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq765
    | (have j0 := eq765 X0 X1
       grind)
    | exact resolve eq765 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq767 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq766 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq766
    | (have j0 := eq766 X0 X1
       grind)
    | exact resolve eq766 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq768 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq767 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq767
    | (have j0 := eq767 X0 X1
       grind)
    | exact resolve eq767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq813 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (τ X0) (τ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq12 X1 (τ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq88 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq827 : ∀ X0 : G, (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq829 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq813 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq830 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq827 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq827
    | (have j0 := eq827 X0
       grind)
    | exact resolve eq827 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq832 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq829
    | (have j0 := eq829 X0 X1
       grind)
    | exact resolve eq829 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq857 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ X0)
       have i₂ := eq830 X0
       grind)
    | exact superpose eq830 eq12
    | (have j0 := eq12 (τ X0) (τ X0)
       have j1 := eq830 X0
       grind)
    | (have r₁ := eq12 (τ X0) (τ X0)
       have r₂ := eq830 X0
       grind)
    | exact resolve eq12 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq871 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq873 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq871 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq871
    | (have j0 := eq871 X0
       grind)
    | exact resolve eq871 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq1476 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq873 X0
       grind)
    | exact superpose eq873 eq11
    | (have j1 := eq873 X0
       grind)
    | exact resolve eq11 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1494 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1476 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1476
    | (have j0 := eq1476 X0
       grind)
    | exact resolve eq1476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1526 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1494 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1494
    | (have j0 := eq1494 (σ X0)
       grind)
    | exact resolve eq1494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494
  have eq1574 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1526 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1526
    | (have j0 := eq1526 X0
       grind)
    | exact resolve eq1526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1575 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1574 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1574
    | (have j0 := eq1574 X0
       grind)
    | exact resolve eq1574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq2425 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq196 X0 X0
       have i₂ := eq1575 X0
       grind)
    | exact superpose eq1575 eq196
    | (have j0 := eq196 X0 X0
       have j1 := eq1575 X0
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq1575 X0
       grind)
    | exact resolve eq196 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq2460 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2425 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq2480 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2460 X0
       have j1 := eq197 X0
       grind)
    | (have r₁ := eq2460 X0
       have r₂ := eq197 X0
       grind)
    | exact resolve eq2460 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq2460
  have eq8642 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X1)
       have i₂ := eq832 X1 X0
       grind)
    | exact superpose eq832 eq12
    | (have j0 := eq12 X0 (τ X1)
       have j1 := eq832 X1 X0
       grind)
    | (have r₁ := eq12 X1 (τ X0)
       have r₂ := eq832 X0 X1
       grind)
    | exact resolve eq12 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq8667 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8642 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8642
  have eq8700 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq8667 X0 X1
       have j1 := eq225 X1 X0
       grind)
    | (have r₁ := eq8667 X0 X0
       have r₂ := eq225 X0 X1
       grind)
    | exact resolve eq8667 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq8667
  have eq8758 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8700 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8700
    | exact resolve eq8700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8700
  have eq8868 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8758 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq8758
    | (have j0 := eq8758 X0 X1
       grind)
    | exact resolve eq8758 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8758
  have eq8926 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq8868 X0 X1
       grind)
    | exact superpose eq8868 eq10
    | (have j1 := eq8868 X0 X1
       grind)
    | exact resolve eq10 eq8868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8982 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8926 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq8926
    | (have j0 := eq8926 X0 X1
       grind)
    | exact resolve eq8926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8926
  have eq9096 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq8982 (σ X0) X1
       grind)
    | exact superpose eq8982 eq22
    | (have j1 := eq8982 (σ X0) X1
       grind)
    | exact resolve eq22 eq8982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8982
  have eq9414 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9096 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9096
    | exact resolve eq9096 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9096
  have eq9523 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9414 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9414
    | (have j0 := eq9414 X0 X1
       grind)
    | exact resolve eq9414 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9414
  have eq9528 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9523 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9523
    | exact resolve eq9523 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9523
  have eq9652 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9528 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9528
    | (have j0 := eq9528 X0 X1
       grind)
    | exact resolve eq9528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9528
  have eq13575 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq9652 X0 X1
       grind)
    | exact superpose eq9652 eq10
    | (have j1 := eq9652 X0 X1
       grind)
    | exact resolve eq10 eq9652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9652
  have eq13653 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13575 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13575
    | (have j0 := eq13575 X0 X1
       grind)
    | exact resolve eq13575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13575
  have eq13917 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13653 (τ X1) (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq13653
    | exact resolve eq13653 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq13653
  have eq14103 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13917 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13917
    | (have j0 := eq13917 X0 X1
       grind)
    | exact resolve eq13917 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13917
  have eq14140 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14103 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14103
    | (have j0 := eq14103 X0 X1
       grind)
    | exact resolve eq14103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14103
  have eq16312 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq353 X0
       have i₂ := eq14140 X0 X0
       grind)
    | exact superpose eq14140 eq353
    | (have j0 := eq353 X0
       have j1 := eq14140 X0 X0
       grind)
    | (have r₁ := eq353 x
       have r₂ := eq14140 x x
       grind)
    | exact resolve eq353 eq14140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16325 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq14140 X1 X0
       grind)
    | exact superpose eq14140 eq11
    | (have j1 := eq14140 X1 X0
       grind)
    | exact resolve eq11 eq14140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14140
  have eq16432 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16325 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq16325
    | (have j0 := eq16325 X0 X1
       grind)
    | exact resolve eq16325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16325
  have eq16439 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq16312 X0
       have j1 := eq353 X0
       grind)
    | (have r₁ := eq16312 X0
       have r₂ := eq353 X0
       grind)
    | exact resolve eq16312 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq16312
  have eq16811 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16432 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq16432
    | exact resolve eq16432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16432
  have eq16967 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16811 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq16811
    | (have j0 := eq16811 X0 X1
       grind)
    | exact resolve eq16811 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16811
  have eq16974 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16967 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16967
    | (have j0 := eq16967 X0 X1
       grind)
    | exact resolve eq16967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16967
  have eq17715 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16974 y x
       grind)
    | exact superpose eq16974 eq16
    | (have j1 := eq16974 y x
       grind)
    | exact resolve eq16 eq16974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16974
  have eq17784 : y = (k y x) := by
    first
    | (have j1 := eq8868 x y
       grind)
    | (have r₁ := eq17715
       have r₂ := eq8868 x y
       grind)
    | exact resolve eq17715 eq8868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8868 eq17715
  have eq17797 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq196 x y
       have i₂ := eq17784
       grind)
    | exact superpose eq17784 eq196
    | (have j0 := eq196 x x
       grind)
    | exact resolve eq196 eq17784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq17799 : y ≠ y ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq768 y x
       have i₂ := eq17784
       grind)
    | exact superpose eq17784 eq768
    | (have j0 := eq768 x x
       grind)
    | (have r₁ := eq768 y x
       have r₂ := eq17784
       grind)
    | exact resolve eq768 eq17784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq17784
  have eq17800 : y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq17799
  have eq17801 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17797
  have eq21997 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17801
       grind)
    | exact superpose eq17801 eq16
    | exact resolve eq16 eq17801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17801
  have eq22020 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21997
       have i₂ := eq17800
       grind)
    | exact superpose eq17800 eq21997
    | exact resolve eq21997 eq17800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17800 eq21997
  have eq22024 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22020
  have eq22346 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2480 x
       have i₂ := eq22024
       grind)
    | exact superpose eq22024 eq2480
    | (have j0 := eq2480 x
       grind)
    | exact resolve eq2480 eq22024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480 eq22024
  have eq22359 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22346
  have eq22360 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22359
  have eq22399 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ x) X1 x
       have i₂ := eq22360
       grind)
    | exact superpose eq22360 eq9
    | exact resolve eq9 eq22360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22420 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq16439 (σ x)
       have i₂ := eq22360
       grind)
    | exact superpose eq22360 eq16439
    | (have j0 := eq16439 (σ x)
       grind)
    | exact resolve eq16439 eq22360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16439
  have eq22429 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by grind
  clear eq22420
  have eq22444 : x = (M.op x x) := by
    first
    | (have i₁ := eq22429
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22429
    | exact resolve eq22429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22429
  have eq22886 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X1 x
       have i₂ := eq22444
       grind)
    | exact superpose eq22444 eq9
    | exact resolve eq9 eq22444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24772 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq22886 x X0
       have i₂ := eq22444
       grind)
    | exact superpose eq22444 eq22886
    | exact resolve eq22886 eq22444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22444 eq22886
  have eq26386 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq22399 (σ x) X0
       have i₂ := eq22360
       grind)
    | exact superpose eq22360 eq22399
    | exact resolve eq22399 eq22360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22360 eq22399
  have eq26601 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26386 (σ y)
       grind)
    | exact superpose eq26386 eq16
    | exact resolve eq16 eq26386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26386
  have eq26680 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq26601
       have i₂ := eq24772 y
       grind)
    | exact superpose eq24772 eq26601
    | exact resolve eq26601 eq24772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24772 eq26601
  have eq26681 : False := by grind
  exact eq26681

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_x_pxx_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq32 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) x X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | (have j1 := eq56 (σ X0)
       grind)
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq101 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 x (M.op X0 X0)
       have i₂ := eq32 X0 x
       grind)
    | (have i₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq32 X0 x
       grind)
    | exact superpose eq32 eq13
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq374 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq376 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq377 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq379 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq377
    | (have j0 := eq377 X0 X1
       grind)
    | exact resolve eq377 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq383 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       have j1 := eq375 X1 X0
       grind)
    | (have r₁ := eq379 X1 X0
       have r₂ := eq375 X0 X1
       grind)
    | (have r₁ := eq379 X1 X1
       have r₂ := eq375 X1 X1
       grind)
    | exact resolve eq379 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq379
  have eq497 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq70 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq507 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq497 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq497
    | (have j0 := eq497 (τ X0)
       grind)
    | exact resolve eq497 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq507 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq507
    | (have j0 := eq507 X0
       grind)
    | exact resolve eq507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq511 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq508 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq508
    | (have j0 := eq508 X0
       grind)
    | exact resolve eq508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq545 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq511 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq511
    | (have j0 := eq511 (τ X0)
       grind)
    | exact resolve eq511 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq511
  have eq596 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq383 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq383
    | exact resolve eq383 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq383 y x
       grind)
    | exact superpose eq383 eq16
    | (have j1 := eq383 x x
       grind)
    | exact resolve eq16 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq626 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq596 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq596
    | (have j0 := eq596 X0 X1
       grind)
    | exact resolve eq596 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq596
  have eq627 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq626
    | (have j0 := eq626 X1 X1
       grind)
    | exact resolve eq626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq685 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq627 (τ X1) X0
       grind)
    | exact superpose eq627 eq17
    | (have j1 := eq627 X0 X0
       grind)
    | exact resolve eq17 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq627
  have eq868 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq685 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq685
    | (have j0 := eq685 X1 X1
       grind)
    | exact resolve eq685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq918 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq868 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq868
    | (have j0 := eq868 X0 X1
       grind)
    | exact resolve eq868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq1022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq608
       have i₂ := eq918 y x
       grind)
    | exact superpose eq918 eq608
    | (have j1 := eq918 x (σ x)
       grind)
    | (have r₁ := eq608
       have r₂ := eq918 y x
       grind)
    | exact resolve eq608 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq918
  have eq1023 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1022
  have eq1055 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1023
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1023
       grind)
    | exact resolve eq12 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1066 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq1055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1074 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq1066 X1
       grind)
    | exact superpose eq1066 eq12
    | (have j0 := eq12 X0 (σ x)
       have j1 := eq1066 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1066 X0
       grind)
    | exact resolve eq12 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1085 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 (σ x)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1074 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1129 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq497 x
       have i₂ := eq1085 X0 x
       grind)
    | exact superpose eq1085 eq497
    | (have j0 := eq497 x
       have j1 := eq1085 X0 x
       grind)
    | exact resolve eq497 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq1085
  have eq1146 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq1129 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1159 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq1146 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq1146 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq1146 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1172 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq545 (σ x)
       have i₂ := eq1159 (σ x)
       grind)
    | exact superpose eq1159 eq545
    | (have j0 := eq545 (σ x)
       grind)
    | exact resolve eq545 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq1176 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56 (σ x)
       have i₂ := eq1159 (σ x)
       grind)
    | exact superpose eq1159 eq56
    | (have j0 := eq56 (σ x)
       grind)
    | exact resolve eq56 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1181 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq1159 (σ X0)
       grind)
    | exact superpose eq1159 eq15
    | exact resolve eq15 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ x)
       have i₂ := eq1159 (σ X0)
       grind)
    | exact superpose eq1159 eq28
    | exact resolve eq28 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1159
  have eq1193 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1176
  have eq1196 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by grind
  clear eq1172
  have eq1201 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1187 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1187
    | exact resolve eq1187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1206 : x = (M.op x x) := by
    first
    | (have i₁ := eq1196
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1196
    | exact resolve eq1196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1213 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1201 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1201
    | exact resolve eq1201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1267 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq102 x x
       have i₂ := eq1206
       grind)
    | exact superpose eq1206 eq102
    | exact resolve eq102 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1270 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1267 X0
       have i₂ := eq1213 x
       grind)
    | exact superpose eq1213 eq1267
    | (have j0 := eq1267 X0
       grind)
    | exact resolve eq1267 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq1267
  have eq1271 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1946 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq102 (σ x) x
       have i₂ := eq1193
       grind)
    | exact superpose eq1193 eq102
    | exact resolve eq102 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1193
  have eq1952 : ∀ X0 : G, (σ (k x x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq1946 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1946
    | (have j0 := eq1946 X0
       grind)
    | exact resolve eq1946 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946
  have eq1955 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq1952 X0
       have i₂ := eq1181 x
       grind)
    | exact superpose eq1181 eq1952
    | (have j0 := eq1952 X0
       grind)
    | exact resolve eq1952 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq1952
  have eq1956 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955
  have eq1961 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1956 (σ y)
       grind)
    | exact superpose eq1956 eq16
    | exact resolve eq16 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq1992 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1961
       have i₂ := eq1271 y
       grind)
    | exact superpose eq1271 eq1961
    | exact resolve eq1961 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq1961
  have eq1993 : False := by grind
  exact eq1993

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation4069 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq109 : ∀ X0 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) x X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 X0 X2
       have i₂ := eq109 X0 X1
       grind)
    | (have i₁ := eq109 X0 X2
       have i₂ := eq109 X0 (M.op X0 X0)
       grind)
    | exact superpose eq109 eq109
    | exact resolve eq109 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq109 (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq109
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq129 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq115
    | exact resolve eq115 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq307 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq312 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq307
    | (have j0 := eq307 X0 X1
       grind)
    | exact resolve eq307 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq469 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 X0 X2
       have i₂ := eq113 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq129 X0 X2
       have i₂ := eq113 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq113 eq129
    | exact resolve eq129 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq557 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 x
       have i₂ := eq469 X0 X1 x
       grind)
    | exact superpose eq469 eq129
    | exact resolve eq129 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq1231 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq312 x y
       grind)
    | exact superpose eq312 eq16
    | (have j1 := eq312 x (M.op x x)
       grind)
    | exact resolve eq16 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq17168 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq309
    | (have j0 := eq309 X1 X1
       grind)
    | exact resolve eq309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq17408 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17168 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq17168
    | (have j0 := eq17168 (M.op X1 X1) X1
       grind)
    | exact resolve eq17168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17168
  have eq161350 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1231
       have i₂ := eq17408 y x
       grind)
    | exact superpose eq17408 eq1231
    | (have j1 := eq17408 (M.op x x) x
       grind)
    | (have r₁ := eq1231
       have r₂ := eq17408 y x
       grind)
    | (have r₁ := eq1231
       have r₂ := eq17408 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1231
       have r₂ := eq17408 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1231 eq17408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq17408
  have eq161351 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq161350
  have eq486392 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq161351
       grind)
    | exact superpose eq161351 eq16
    | exact resolve eq16 eq161351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161351
  have eq486393 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq486392
       have r₂ := eq22 x
       grind)
    | exact resolve eq486392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486392
  have eq486395 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq486393
       grind)
    | exact superpose eq486393 eq10
    | exact resolve eq10 eq486393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486393
  have eq486458 : x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq486395
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq486395
    | exact resolve eq486395 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486395
  have eq486460 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq486458
       grind)
    | exact superpose eq486458 eq16
    | exact resolve eq16 eq486458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486458
  have eq486461 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq486460
       have r₂ := eq22 x
       grind)
    | exact resolve eq486460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq486460
  have eq488422 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq486461
       grind)
    | exact superpose eq486461 eq10
    | exact resolve eq10 eq486461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486461
  have eq488488 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq488422
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq488422
    | exact resolve eq488422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488422
  have eq488489 : x = (M.op x x) := by grind
  clear eq488488
  have eq488508 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X1 x
       have i₂ := eq488489
       grind)
    | exact superpose eq488489 eq9
    | exact resolve eq9 eq488489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488552 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq557 x x
       have i₂ := eq488489
       grind)
    | exact superpose eq488489 eq557
    | exact resolve eq557 eq488489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq489017 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq488552 X0
       have i₂ := eq488489
       grind)
    | exact superpose eq488489 eq488552
    | exact resolve eq488552 eq488489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488489 eq488552
  have eq493745 : ∀ X0 X1 : G, (M.op (σ x) X0) = (σ (M.op (M.op x x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq469 x X1 X0
       have i₂ := eq489017 x
       grind)
    | exact superpose eq489017 eq469
    | exact resolve eq469 eq489017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq494147 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq493745 X0 x
       have i₂ := eq488508 x x
       grind)
    | exact superpose eq488508 eq493745
    | exact resolve eq493745 eq488508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488508 eq493745
  have eq495815 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq494147 (σ y)
       grind)
    | exact superpose eq494147 eq16
    | exact resolve eq16 eq494147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494147
  have eq496640 : False := by grind
  exact eq496640

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyy_pxy_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) y) X0) := by
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
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X2
       have i₂ := eq16 X0 X1 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq177 X0 x X2 X3
       have i₂ := eq16 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) X2) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq332 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq332 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq332
    | exact resolve eq332 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq616 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 x X2
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq180 X0 X0 X2
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1003 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq1004 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) ≠ (M.op (M.op (M.op X0 X1) X1) X2) ∨ (M.op (M.op (M.op X0 X1) X1) X2) = X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq12
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1123 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = X0 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1097 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1130 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1116 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1116 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1145 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1123 X0 X1 X2
       have j1 := eq183 X0 X1 X2 X0
       grind)
    | (have r₁ := eq1123 X0 X1 X2
       have r₂ := eq183 X0 X1 X2 x
       grind)
    | exact resolve eq1123 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1123
  have eq1216 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X2 x
       have i₂ := eq1130 X0
       grind)
    | exact superpose eq1130 eq182
    | exact resolve eq182 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1 (M.op X0 X0)
       have i₂ := eq1130 (M.op X0 X0)
       grind)
    | exact superpose eq1130 eq616
    | exact resolve eq616 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq1229 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (M.op X0 X0) X1
       have i₂ := eq1130 (M.op X0 X0)
       grind)
    | exact superpose eq1130 eq182
    | exact resolve eq182 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1241 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (k x x) X0) := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq1130 x
       grind)
    | exact superpose eq1130 eq185
    | exact resolve eq185 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1256 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k x x) X0) := by
    intro X0
    first
    | (have i₁ := eq1241 X0
       have i₂ := eq1130 sF0
       grind)
    | exact superpose eq1130 eq1241
    | exact resolve eq1241 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1268 : ∀ X0 X1 : G, (k X0 X0) = (M.op (k (k X0 X0) (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1229 X0 X1
       have i₂ := eq1130 X0
       grind)
    | exact superpose eq1130 eq1229
    | exact resolve eq1229 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1270 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 X0 X1
       have i₂ := eq1130 X0
       grind)
    | exact superpose eq1130 eq1227
    | exact resolve eq1227 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1480 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (M.op (τ X0) X1) X1) X2)) = (k X0 (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq1145 (τ X0) X1 X2
       grind)
    | exact superpose eq1145 eq34
    | exact resolve eq34 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1145
  have eq1481 : ∀ X0 X1 X2 : G, (k X0 X0) = (σ (M.op (M.op (M.op (τ X0) X1) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1480 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1480
    | exact resolve eq1480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480
  have eq1659 : ∀ X0 X1 X2 : G, (τ (k X0 X0)) = (M.op (M.op (τ (k X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1216 (τ X0) X1 X2
       have i₂ := eq416 X0 X0
       grind)
    | exact superpose eq416 eq1216
    | exact resolve eq1216 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq1216
  have eq2322 : ∀ X0 X1 X2 X3 : G, (k X0 X0) = (M.op (σ (M.op (M.op (M.op (τ (k X0 X0)) X1) X1) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1268 X0 X3
       have i₂ := eq1481 (k X0 X0) X1 X2
       grind)
    | exact superpose eq1481 eq1268
    | exact resolve eq1268 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268 eq1481
  have eq2348 : ∀ X0 X2 X3 : G, (k X0 X0) = (M.op (σ (M.op (τ (k X0 X0)) X2)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2322 X0 x X2 X3
       have i₂ := eq1659 X0 x x
       grind)
    | exact superpose eq1659 eq2322
    | exact resolve eq2322 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659 eq2322
  have eq4586 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1003
       grind)
    | exact superpose eq1003 eq39
    | exact resolve eq39 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq4587 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4586
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4586
    | exact resolve eq4586 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4586
  have eq4589 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4587
    | exact resolve eq4587 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq4591 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq4589
       have i₂ := eq1130 x
       grind)
    | exact superpose eq1130 eq4589
    | exact resolve eq4589 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589
  have eq5384 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ (M.op (k x x) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq97 eq2348
    | exact resolve eq2348 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2348
  have eq5447 : ∀ X1 : G, (k (σ x) (σ x)) = (M.op (σ (k (M.op x y) (M.op x y))) X1) := by
    intro X1
    first
    | (have i₁ := eq5384 x X1
       have i₂ := eq1256 x
       grind)
    | exact superpose eq1256 eq5384
    | exact resolve eq5384 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256 eq5384
  have eq5474 : ∀ X1 : G, (k (σ x) (σ x)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X1) := by
    intro X1
    first
    | exact superpose eq41 eq5447
    | exact resolve eq5447 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq5447
  have eq5490 : ∀ X1 : G, (k (σ x) (σ x)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X1) := by
    intro X1
    first
    | exact superpose eq20 eq5474
    | (have j0 := eq5474 X1
       grind)
    | exact resolve eq5474 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5474
  have eq51253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4591 eq1004
    | exact resolve eq1004 eq4591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51262 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq51253
       have r₂ := eq27
       grind)
    | exact resolve eq51253 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51253
  have eq51269 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq51262
       have i₂ := eq1130 sF2
       grind)
    | exact superpose eq1130 eq51262
    | exact resolve eq51262 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51262
  have eq51274 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq51269 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq51269
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq51269
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq51269
       grind)
    | exact resolve eq12 eq51269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51269
  have eq51328 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq51274
       have r₂ := eq26
       grind)
    | exact resolve eq51274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51274
  have eq51347 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq51328
       have i₂ := eq1130 sF2
       grind)
    | exact superpose eq1130 eq51328
    | exact resolve eq51328 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51328
  have eq51348 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq51347
  have eq51362 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq4591 eq51348
    | exact resolve eq51348 eq4591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4591 eq51348
  have eq51373 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq51362
       have r₂ := eq27
       grind)
    | exact resolve eq51362 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51362
  have eq51385 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq51373 eq141
    | exact resolve eq141 eq51373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51373
  have eq51423 : x = (k x x) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29 eq51385
    | exact resolve eq51385 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51385
  have eq51424 : (M.op x y) = (M.op y x) ∨ x = (k x x) := by grind
  clear eq51423
  have eq51444 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq51424
       grind)
    | exact superpose eq51424 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq51424
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq51424
       grind)
    | exact resolve eq12 eq51424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51424
  have eq51496 : x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq51444
       have r₂ := eq18
       grind)
    | exact resolve eq51444 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51444
  have eq51514 : x = (k x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq51496
       have i₂ := eq1130 x
       grind)
    | exact superpose eq1130 eq51496
    | exact resolve eq51496 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51496
  have eq51515 : (M.op x y) = (k y x) ∨ x = (k x x) := by grind
  clear eq51514
  have eq51539 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq51515
       grind)
    | exact superpose eq51515 eq39
    | exact resolve eq39 eq51515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51515
  have eq51541 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq51539
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51539
    | exact resolve eq51539 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq51539
  have eq51545 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq51541
    | exact resolve eq51541 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51541
  have eq51550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq51545 eq1004
    | exact resolve eq1004 eq51545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq51559 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq51550
       have r₂ := eq27
       grind)
    | exact resolve eq51550 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51550
  have eq51566 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq51559
       have i₂ := eq1130 sF2
       grind)
    | exact superpose eq1130 eq51559
    | exact resolve eq51559 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51559
  have eq52537 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq51566 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq51566
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq51566
       grind)
    | exact resolve eq12 eq51566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51566
  have eq52595 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq52537
       have r₂ := eq26
       grind)
    | exact resolve eq52537 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52537
  have eq52619 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq52595
       have i₂ := eq1130 sF2
       grind)
    | exact superpose eq1130 eq52595
    | exact resolve eq52595 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq52595
  have eq52620 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by grind
  clear eq52619
  have eq52638 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq51545 eq52620
    | exact resolve eq52620 eq51545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51545 eq52620
  have eq52649 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq52638
       have r₂ := eq27
       grind)
    | exact resolve eq52638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52638
  have eq52663 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) := by
    first
    | exact superpose eq52649 eq141
    | exact resolve eq141 eq52649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq52649
  have eq52701 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq52663
    | exact resolve eq52663 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52663
  have eq52702 : x = (k x x) := by grind
  clear eq52701
  have eq52727 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq52702
       grind)
    | exact superpose eq52702 eq39
    | exact resolve eq39 eq52702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq52735 : ∀ X0 : G, (k x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1270 x x
       have i₂ := eq52702
       grind)
    | exact superpose eq52702 eq1270
    | exact resolve eq1270 eq52702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq52761 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq52735 X0
       have i₂ := eq52702
       grind)
    | exact superpose eq52702 eq52735
    | exact resolve eq52735 eq52702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52702 eq52735
  have eq52766 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq52727
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52727
    | exact resolve eq52727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52727
  have eq52925 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq52761 y
       grind)
    | exact superpose eq52761 eq18
    | (have j1 := eq52761 y
       grind)
    | exact resolve eq18 eq52761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52761
  have eq53074 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq52925
       grind)
    | exact superpose eq52925 eq22
    | exact resolve eq22 eq52925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq52925
  have eq53162 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq53074 eq20
    | exact resolve eq20 eq53074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq53074
  have eq53521 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq53162 eq5490
    | exact resolve eq5490 eq53162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5490
  have eq53528 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq52766 eq53521
    | exact resolve eq53521 eq52766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52766 eq53521
  have eq54733 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53528 eq26
    | (have j1 := eq53528 (σ y)
       grind)
    | exact resolve eq26 eq53528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53528
  have eq54864 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq54733 eq27
    | exact resolve eq27 eq54733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq54733
  have eq54888 : False := by grind
  exact eq54888

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_x_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 X3) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X2
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63
    | (have j0 := eq63 (σ X0) (σ X1)
       grind)
    | exact resolve eq63 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq63 X1 (τ X0)
       grind)
    | exact superpose eq63 eq18
    | (have j1 := eq63 X1 (τ X0)
       grind)
    | exact resolve eq18 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq128 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 (M.op X0 X1) X1 X2
       have i₂ := eq9 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq9 eq27
    | exact resolve eq27 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq222 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X3) X4) = (k X4 (M.op (M.op X0 X3) X3)) ∨ (M.op (M.op (M.op X0 X1) X1) X2) ≠ (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X4 (M.op (M.op X0 X3) X3)
       have i₂ := eq23 X0 X3 (M.op (M.op X0 X3) X3) X1 X2
       grind)
    | (have i₁ := eq12 X4 (M.op (M.op X0 X3) X3)
       have i₂ := eq23 X0 X1 X2 X3 (M.op (M.op X0 X3) X3)
       grind)
    | exact superpose eq23 eq12
    | (have j0 := eq12 X4 (M.op (M.op X0 X3) X3)
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq496 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq16
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq792 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq80 X0 (τ X0)
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq80 X0 (τ X0)
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq80 X0 (τ X0)
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq804 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq792 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq806 : ∀ X0 X1 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq804 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq804
    | (have j0 := eq804 X0 X1
       grind)
    | exact resolve eq804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq496
       have i₂ := eq63 y x
       grind)
    | exact superpose eq63 eq496
    | (have j1 := eq63 (σ y) (σ x)
       grind)
    | exact resolve eq496 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq818 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq815
  have eq819 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq9
    | exact resolve eq9 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq819 X0
       grind)
    | exact superpose eq819 eq16
    | (have j1 := eq819 X0
       grind)
    | exact resolve eq16 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq1183 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1168 X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq1168
    | exact resolve eq1168 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1184 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq6945 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq806 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq806
    | exact resolve eq806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq6994 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6945 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6945
    | (have j0 := eq6945 X0 X1
       grind)
    | exact resolve eq6945 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6945
  have eq7014 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq6994 X0 X1
       grind)
    | exact superpose eq6994 eq10
    | (have j1 := eq6994 X0 X1
       grind)
    | exact resolve eq10 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6994
  have eq7053 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7014 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7014
    | (have j0 := eq7014 X0 X0
       grind)
    | exact resolve eq7014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7014
  have eq7108 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7053 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7053
  have eq7109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7108
  have eq7161 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7109 (σ X0)
       grind)
    | exact superpose eq7109 eq15
    | exact resolve eq15 eq7109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7187 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7161 X0
       have i₂ := eq7109 X0
       grind)
    | exact superpose eq7109 eq7161
    | exact resolve eq7161 eq7109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7109 eq7161
  have eq20132 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) ≠ (M.op (M.op (M.op x X1) X1) X2) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222 x X1 X2 y x
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq222
    | exact resolve eq222 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq20218 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20132 X0 x x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq20132
    | (have j0 := eq20132 X0 x x
       grind)
    | exact resolve eq20132 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20132
  have eq20286 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq20218 X0
       grind)
    | (have r₁ := eq20218 X0
       have r₂ := eq1184 y
       grind)
    | exact resolve eq20218 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq20218
  have eq2240639 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20286 X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq20286
    | exact resolve eq20286 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq20286
  have eq2240924 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2240639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2240639
  have eq2290065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq496
       have i₂ := eq2240924 y
       grind)
    | exact superpose eq2240924 eq496
    | exact resolve eq496 eq2240924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq2240924
  have eq2290066 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2290065
  have eq2290067 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2290066
  have eq2290157 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2290067
       grind)
    | exact superpose eq2290067 eq16
    | exact resolve eq16 eq2290067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2290259 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq2290067
       grind)
    | exact superpose eq2290067 eq9
    | exact resolve eq9 eq2290067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2291003 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2290259 X0
       have i₂ := eq2290067
       grind)
    | exact superpose eq2290067 eq2290259
    | exact resolve eq2290259 eq2290067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290259
  have eq2291366 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2291003 X0
       have i₂ := eq7187 x
       grind)
    | exact superpose eq7187 eq2291003
    | exact resolve eq2291003 eq7187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7187 eq2291003
  have eq2292679 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2291366 (σ y)
       have i₂ := eq2290067
       grind)
    | exact superpose eq2290067 eq2291366
    | exact resolve eq2291366 eq2290067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290067 eq2291366
  have eq2296435 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2292679
       grind)
    | exact superpose eq2292679 eq10
    | exact resolve eq10 eq2292679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292679
  have eq2297107 : x = (M.op x x) := by
    first
    | (have i₁ := eq2296435
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2296435
    | exact resolve eq2296435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296435
  have eq2297848 : ∀ X0 : G, x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq128 x x x
       have i₂ := eq2297107
       grind)
    | exact superpose eq2297107 eq128
    | exact resolve eq128 eq2297107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq2298486 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2297848 X0
       have i₂ := eq2297107
       grind)
    | exact superpose eq2297107 eq2297848
    | exact resolve eq2297848 eq2297107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297107 eq2297848
  have eq2299833 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2290157
       have i₂ := eq2298486 y
       grind)
    | exact superpose eq2298486 eq2290157
    | exact resolve eq2290157 eq2298486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290157 eq2298486
  have eq2300556 : False := by grind
  exact eq2300556

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_y_y_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  clear eq40
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
  have eq175 : y ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq708 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq745 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq760 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq712 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq773 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq760 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq760 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq760 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq760 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq785 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq773 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq773
    | (have j0 := eq773 (σ X0) X1
       grind)
    | exact resolve eq773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq707
       grind)
    | exact superpose eq707 eq41
    | exact resolve eq41 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq840
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq840
    | exact resolve eq840 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq843 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq841
    | exact resolve eq841 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq843 eq708
    | exact resolve eq708 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq887 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq880
       have r₂ := eq27
       grind)
    | exact resolve eq880 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq902 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq887 eq28
    | (have j0 := eq28 (σ x) (σ x)
       grind)
    | (have r₁ := eq28 (σ x) (σ x)
       have r₂ := eq887
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq887
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq887
       grind)
    | exact resolve eq28 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq903 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq902
  have eq912 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq903 eq142
    | exact resolve eq142 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq919 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq912
    | exact resolve eq912 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq922 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq919
       have r₂ := eq13 x x
       grind)
    | exact resolve eq919 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq928 : ∀ X0 : G, x ≠ x ∨ (k x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq773 x X0
       have i₂ := eq922
       grind)
    | exact superpose eq922 eq773
    | (have j0 := eq773 x X0
       grind)
    | (have r₁ := eq773 x x
       have r₂ := eq922
       grind)
    | exact resolve eq773 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq922
  have eq931 : ∀ X0 : G, (k x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq964 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq931 y
       grind)
    | exact superpose eq931 eq41
    | exact resolve eq41 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq931
  have eq978 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq964
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq964
    | exact resolve eq964 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq984 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq978
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq978
    | exact resolve eq978 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq986 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq984
       have r₂ := eq176
       grind)
    | exact resolve eq984 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq984
  have eq992 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq986 eq91
    | exact resolve eq91 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq986
  have eq999 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq992
    | exact resolve eq992 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq992
  have eq1002 : y = (k x y) := by
    first
    | (have r₁ := eq999
       have r₂ := eq175
       grind)
    | exact resolve eq999 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq999
  have eq1006 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq707
       have i₂ := eq1002
       grind)
    | exact superpose eq1002 eq707
    | exact resolve eq707 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq1007 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq1002
       grind)
    | exact superpose eq1002 eq36
    | exact resolve eq36 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1002
  have eq1009 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1006
  have eq1012 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1007
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1007
    | exact resolve eq1007 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1017 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1012 eq708
    | exact resolve eq708 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq1012
  have eq1021 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1017
  have eq1036 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq534 x x x
       have i₂ := eq1009
       grind)
    | exact superpose eq1009 eq534
    | exact resolve eq534 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq1009
       grind)
    | exact superpose eq1009 eq28
    | (have j0 := eq28 x x
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq1009
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq1009
       grind)
    | exact resolve eq28 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq1038
  have eq1042 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1009 eq1036
    | exact resolve eq1036 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009 eq1036
  have eq1054 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1021 eq534
    | exact resolve eq534 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1021 eq28
    | (have j0 := eq28 (σ x) (σ x)
       grind)
    | (have r₁ := eq28 (σ x) (σ x)
       have r₂ := eq1021
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq1021
       grind)
    | exact resolve eq28 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1057 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1056
  have eq1060 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1021 eq1054
    | exact resolve eq1054 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq1054
  have eq1066 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq785 x X0
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq785
    | (have j0 := eq785 x X0
       grind)
    | exact resolve eq785 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq1039
  have eq1071 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1066 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1072 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1071 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1071
    | (have j0 := eq1071 X0
       grind)
    | exact resolve eq1071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1108 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1042 y
       grind)
    | exact superpose eq1042 eq18
    | (have j1 := eq1042 y
       grind)
    | exact resolve eq18 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1125 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1108
       grind)
    | exact superpose eq1108 eq18
    | exact resolve eq18 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1126 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1108
       grind)
    | exact superpose eq1108 eq24
    | exact resolve eq24 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1134 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1126
    | exact resolve eq1126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1180 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1057 eq142
    | exact resolve eq142 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1057
  have eq1187 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq1180
    | exact resolve eq1180 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1180
  have eq1232 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1060 eq26
    | (have j1 := eq1060 (σ y)
       grind)
    | exact resolve eq26 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1249 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1232 eq27
    | exact resolve eq27 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1255 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1232
  have eq1257 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1134 eq1249
    | (have r₁ := eq1249
       have r₂ := eq1134
       grind)
    | exact resolve eq1249 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1258 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1257
  have eq1387 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1258 eq27
    | exact resolve eq27 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1393 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1134 eq1387
    | exact resolve eq1387 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq1387
  have eq1394 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq1393
  have eq1438 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1072 eq746
    | (have j0 := eq746 (σ x)
       grind)
    | (have r₁ := eq746 (σ x)
       have r₂ := eq1072 (σ x)
       grind)
    | exact resolve eq746 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1447 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1438
  have eq1532 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq746 x
       have i₂ := eq1187
       grind)
    | exact superpose eq1187 eq746
    | (have j0 := eq746 x
       grind)
    | (have r₁ := eq746 x
       have r₂ := eq1187
       grind)
    | exact resolve eq746 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq1187
  have eq1533 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1532
  have eq1584 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1447 eq534
    | exact resolve eq534 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1590 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1447 eq1584
    | exact resolve eq1584 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447 eq1584
  have eq1673 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq534 x x x
       have i₂ := eq1533
       grind)
    | exact superpose eq1533 eq534
    | exact resolve eq534 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq1679 : ∀ X0 : G, x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1533 eq1673
    | exact resolve eq1673 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq1673
  have eq1684 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1590 eq26
    | (have j1 := eq1590 (σ y)
       grind)
    | exact resolve eq26 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1590
  have eq1705 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1684 eq27
    | exact resolve eq27 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1806 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1125
       have i₂ := eq1679 sF0
       grind)
    | exact superpose eq1679 eq1125
    | (have j1 := eq1679 y
       grind)
    | exact resolve eq1125 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq1679
  have eq1817 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1806
  have eq1822 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1258 eq1817
    | exact resolve eq1817 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq1817
  have eq1826 : x = (M.op x y) := by
    first
    | (have r₁ := eq1822
       have r₂ := eq1394
       grind)
    | exact resolve eq1822 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394 eq1822
  have eq1831 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1826
       grind)
    | exact superpose eq1826 eq22
    | exact resolve eq22 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1826
  have eq1856 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1831 eq20
    | exact resolve eq20 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1897 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1856 eq1705
    | (have r₁ := eq1705
       have r₂ := eq1856
       grind)
    | exact resolve eq1705 eq1856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq1898 : y = (M.op x y) := by grind
  clear eq1897
  have eq1917 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1898
       grind)
    | exact superpose eq1898 eq24
    | exact resolve eq24 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1898
  have eq1927 : (σ x) = (σ y) := by
    first
    | exact superpose eq1831 eq1917
    | exact resolve eq1917 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831 eq1917
  have eq1944 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1927 eq1255
    | (have r₁ := eq1255
       have r₂ := eq1927
       grind)
    | exact resolve eq1255 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq1927
  have eq1947 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1944
  have eq2289 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1947 eq27
    | exact resolve eq27 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1947
  have eq2301 : False := by grind
  exact eq2301
