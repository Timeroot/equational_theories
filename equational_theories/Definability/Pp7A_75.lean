import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_y_pxy_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq76 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq9
    | exact resolve eq9 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq125 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq140 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq125
    | (have j0 := eq125 X0 X1
       grind)
    | exact resolve eq125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq125
  have eq148 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq140 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq140 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq307 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq148
    | exact resolve eq148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq148 (σ X1) X0
       grind)
    | exact superpose eq148 eq15
    | (have j1 := eq148 (σ X1) X0
       grind)
    | exact resolve eq15 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq371 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq307 (τ X0) X1
       grind)
    | exact superpose eq307 eq17
    | (have j1 := eq307 (τ X0) X1
       grind)
    | exact resolve eq17 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq307
  have eq864 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq371 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq371
    | exact resolve eq371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq922 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq864
    | (have j0 := eq864 X0 X1
       grind)
    | exact resolve eq864 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq1488 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq314 x y
       grind)
    | exact superpose eq314 eq16
    | (have j1 := eq314 x y
       grind)
    | exact resolve eq16 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1506 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq314 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq1856 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1488
       have i₂ := eq922 x y
       grind)
    | exact superpose eq922 eq1488
    | (have j1 := eq922 (σ x) (σ y)
       grind)
    | (have r₁ := eq1488
       have r₂ := eq922 x y
       grind)
    | exact resolve eq1488 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1857 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1856
  have eq1862 : y ≠ y ∨ y = (k x y) ∨ (M.op x x) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1857
       grind)
    | exact superpose eq1857 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1857
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1857
       grind)
    | exact resolve eq13 eq1857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq1864 : (M.op x x) = (M.op y x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1862
  have eq11386 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1864
       grind)
    | exact superpose eq1864 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1864
       grind)
    | exact resolve eq12 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq11397 : y = (k x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11386
  have eq13647 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1506 x y
       have i₂ := eq11397
       grind)
    | exact superpose eq11397 eq1506
    | (have j0 := eq1506 x y
       grind)
    | exact resolve eq1506 eq11397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506 eq11397
  have eq13668 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq13647
  have eq13669 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13668
  have eq13683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1488
       have i₂ := eq13669
       grind)
    | exact superpose eq13669 eq1488
    | exact resolve eq1488 eq13669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488 eq13669
  have eq13706 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13683
  have eq13707 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13706
  have eq13848 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13707
       grind)
    | exact superpose eq13707 eq16
    | exact resolve eq16 eq13707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13850 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq13707
       grind)
    | exact superpose eq13707 eq9
    | exact resolve eq9 eq13707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13851 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq13707
       grind)
    | exact superpose eq13707 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13707
       grind)
    | exact resolve eq13 eq13707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13858 : (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq13851
  have eq13865 : (σ y) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13858
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq13858
    | exact resolve eq13858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13858
  have eq13866 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq13850
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq13850
    | exact resolve eq13850 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13850
  have eq13872 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq13865
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq13865
    | exact resolve eq13865 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13865
  have eq14040 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq76 y
       have i₂ := eq13866
       grind)
    | exact superpose eq13866 eq76
    | exact resolve eq76 eq13866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq13866
  have eq14076 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq14040
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq14040
    | exact resolve eq14040 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq14040
  have eq14170 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq14076
       grind)
    | exact superpose eq14076 eq77
    | (have j0 := eq77 y X0
       grind)
    | exact resolve eq77 eq14076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14076
  have eq17958 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14170 (σ x)
       have i₂ := eq13707
       grind)
    | exact superpose eq13707 eq14170
    | (have j0 := eq14170 (σ x)
       grind)
    | (have r₁ := eq14170 (σ x)
       have r₂ := eq13707
       grind)
    | exact resolve eq14170 eq13707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14170
  have eq17979 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
  clear eq17958
  have eq17998 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq17979
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17979
    | exact resolve eq17979 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17979
  have eq18195 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq17998
       grind)
    | exact superpose eq17998 eq77
    | (have j0 := eq77 x (σ y)
       grind)
    | exact resolve eq77 eq17998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq18221 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x x)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq18195
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18195
    | exact resolve eq18195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18195
  have eq18251 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq18221
       have i₂ := eq13707
       grind)
    | exact superpose eq13707 eq18221
    | exact resolve eq18221 eq13707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13707 eq18221
  have eq18896 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq17998
       have i₂ := eq13872
       grind)
    | exact superpose eq13872 eq17998
    | exact resolve eq17998 eq13872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13872 eq17998
  have eq18958 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq18896
       have r₂ := eq18251
       grind)
    | exact resolve eq18896 eq18251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18251 eq18896
  have eq19178 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq922 x y
       have i₂ := eq18958
       grind)
    | exact superpose eq18958 eq922
    | (have j0 := eq922 x y
       grind)
    | exact resolve eq922 eq18958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq18958
  have eq19302 : y = (M.op x y) := by
    first
    | (have r₁ := eq19178
       have r₂ := eq13848
       grind)
    | exact resolve eq19178 eq13848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19178
  have eq19474 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq13848
       have i₂ := eq19302
       grind)
    | exact superpose eq19302 eq13848
    | exact resolve eq13848 eq19302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13848 eq19302
  have eq19488 : False := by grind
  exact eq19488

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_x_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq419 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq9
    | (have j1 := eq385 X0 X1
       grind)
    | exact resolve eq9 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq566 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq419 X0 X1
       grind)
    | exact superpose eq419 eq9
    | (have j1 := eq419 X0 X1
       grind)
    | exact resolve eq9 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq571 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq566 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq566 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq566 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq616 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq571 (σ X0) (σ X1)
       grind)
    | exact superpose eq571 eq15
    | exact resolve eq15 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq571 X0 X1
       grind)
    | exact superpose eq571 eq616
    | exact resolve eq616 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq616
  have eq979 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq643 x y
       grind)
    | exact superpose eq643 eq16
    | (have r₁ := eq16
       have r₂ := eq643 x y
       grind)
    | exact resolve eq16 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq995 : False := by grind
  exact eq995

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_x_pxy_pyx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq9
    | (have j1 := eq385 X0 X1
       grind)
    | exact resolve eq9 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq949 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq418 X0 X1
       grind)
    | exact superpose eq418 eq9
    | (have j1 := eq418 X0 X1
       grind)
    | exact resolve eq9 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq959 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq949 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq949 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq949 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq987 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq959 (σ X0) (σ X1)
       grind)
    | exact superpose eq959 eq15
    | exact resolve eq15 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq987 X0 X1
       have i₂ := eq959 X0 X1
       grind)
    | exact superpose eq959 eq987
    | exact resolve eq987 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq987
  have eq1400 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1014 x y
       grind)
    | exact superpose eq1014 eq16
    | (have r₁ := eq16
       have r₂ := eq1014 x y
       grind)
    | exact resolve eq16 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1421 : False := by grind
  exact eq1421

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pxy_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq22
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
  clear eq24 eq35
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq43
    | exact resolve eq43 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq68 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq62 sF2
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq73 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq73 x y
       grind)
    | exact superpose eq73 eq44
    | (have j1 := eq73 x y
       grind)
    | exact resolve eq44 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq88
    | exact resolve eq88 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq118 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq91 eq73
    | (have j0 := eq73 (σ x) (σ y)
       grind)
    | exact resolve eq73 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq776
    | exact resolve eq776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq780 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq777
       have r₂ := eq27
       grind)
    | exact resolve eq777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq782 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq780
    | exact resolve eq780 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq784 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq782 eq119
    | (have r₁ := eq119
       have r₂ := eq782
       grind)
    | exact resolve eq119 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq782
  have eq792 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq784
  have eq816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq792 eq91
    | exact resolve eq91 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq816
  have eq821 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq819
       have r₂ := eq27
       grind)
    | exact resolve eq819 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq824 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq821 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq821
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq821
       grind)
    | exact resolve eq13 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq826 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq824
       have r₂ := eq26
       grind)
    | exact resolve eq824 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq828 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq826
    | exact resolve eq826 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq828 eq91
    | exact resolve eq91 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq828
  have eq851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq848
  have eq853 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq851
       have r₂ := eq27
       grind)
    | exact resolve eq851 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq856 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq853
       grind)
    | exact superpose eq853 eq118
    | (have r₁ := eq118
       have r₂ := eq853
       grind)
    | exact resolve eq118 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq857 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq853
       grind)
    | exact superpose eq853 eq68
    | exact resolve eq68 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq853
  have eq866 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq856
  have eq869 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq857
    | exact resolve eq857 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq999 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq866
       grind)
    | exact superpose eq866 eq44
    | exact resolve eq44 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq1001 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq999
    | exact resolve eq999 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1001 eq73
    | (have j0 := eq73 (σ x) (σ y)
       grind)
    | exact resolve eq73 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1008
    | exact resolve eq1008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1012 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1009
       have r₂ := eq27
       grind)
    | exact resolve eq1009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq869 eq1012
    | exact resolve eq1012 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq1014
    | exact resolve eq1014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1018 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1016
       have r₂ := eq27
       grind)
    | exact resolve eq1016 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1075 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1018
       grind)
    | exact superpose eq1018 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1018
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1018
       grind)
    | exact resolve eq13 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1077 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq1075
       have r₂ := eq18
       grind)
    | exact resolve eq1075 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1079 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1077
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1077
    | exact resolve eq1077 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1077
  have eq1141 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1079
       grind)
    | exact superpose eq1079 eq44
    | exact resolve eq44 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1079
  have eq1143 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1141
    | exact resolve eq1141 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1141
  have eq1156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1143 eq73
    | (have j0 := eq73 (σ x) (σ y)
       grind)
    | exact resolve eq73 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1143
  have eq1157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1156
    | exact resolve eq1156 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1160 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1157
       have r₂ := eq27
       grind)
    | exact resolve eq1157 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq869 eq1160
    | exact resolve eq1160 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq1160
  have eq1164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1162
    | exact resolve eq1162 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1162
  have eq1166 : False := by grind
  exact eq1166

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_x_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  clear eq18
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq396 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2984 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq396 X0 X1
       grind)
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq396 X0 X1
       grind)
    | exact superpose eq396 eq12
    | (have j1 := eq396 X0 X1
       grind)
    | (have r₁ := eq12 X1 (σ X0)
       have r₂ := eq396 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq396 X0 X1
       grind)
    | exact resolve eq12 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq2988 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2984 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984
  have eq4304 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq2988 X0 X1
       grind)
    | exact superpose eq2988 eq23
    | (have j1 := eq2988 X0 X1
       grind)
    | exact resolve eq23 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2988
  have eq4341 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4304 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4304
  have eq4355 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4341 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4341
    | exact resolve eq4341 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq4458 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4355 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq4355
    | (have j0 := eq4355 (τ (k X1 X0)) (τ (M.op X0 X1))
       grind)
    | exact resolve eq4355 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4355
  have eq4491 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq4458 X0 X1
       grind)
    | exact superpose eq4458 eq11
    | (have j1 := eq4458 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq4458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4458
  have eq4609 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4491 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4491
    | (have j0 := eq4491 (M.op X0 X1) (k X1 X0)
       grind)
    | exact resolve eq4491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4491
  have eq4640 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq4609 (τ X0) X1
       grind)
    | exact superpose eq4609 eq19
    | (have j1 := eq4609 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq4609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4662 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4609 (σ X0) (σ X1)
       grind)
    | exact superpose eq4609 eq15
    | (have j1 := eq4609 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4609
  have eq4899 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4640 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4640
    | exact resolve eq4640 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640
  have eq4969 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4899 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4899
    | (have j0 := eq4899 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq4899 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4899
  have eq5339 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4662 x y
       grind)
    | exact superpose eq4662 eq16
    | (have j1 := eq4662 x y
       grind)
    | exact resolve eq16 eq4662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq5376 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5339
       have i₂ := eq4969 x y
       grind)
    | exact superpose eq4969 eq5339
    | (have j1 := eq4969 (σ x) (σ y)
       grind)
    | (have r₁ := eq5339
       have r₂ := eq4969 x y
       grind)
    | (have r₁ := eq5339
       have r₂ := eq4969 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5339
       have r₂ := eq4969 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5339 eq4969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4969 eq5339
  have eq5379 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5376
  have eq5383 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5379
       grind)
    | exact superpose eq5379 eq16
    | exact resolve eq16 eq5379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5379
  have eq5384 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5383
       have r₂ := eq77 x
       grind)
    | exact resolve eq5383 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5383
  have eq5385 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5384
       grind)
    | exact superpose eq5384 eq16
    | exact resolve eq16 eq5384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5386 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5384
       grind)
    | exact superpose eq5384 eq10
    | exact resolve eq10 eq5384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5384
  have eq5440 : x = y := by
    first
    | (have i₁ := eq5386
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5386
    | exact resolve eq5386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5386
  have eq5441 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5385
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq5385
    | exact resolve eq5385 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq5385
  have eq5442 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5441
       have i₂ := eq5440
       grind)
    | exact superpose eq5440 eq5441
    | exact resolve eq5441 eq5440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5440 eq5441
  have eq5443 : False := by grind
  exact eq5443

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq32 (τ X0)
       grind)
    | exact superpose eq32 eq18
    | exact resolve eq18 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq37
    | exact resolve eq37 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq37
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq128 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq156 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq128
    | (have j0 := eq128 X0 X1
       grind)
    | exact resolve eq128 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq128
  have eq160 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq156 X1 (τ X1)
       have r₂ := eq79 (τ X1) X1
       grind)
    | (have r₁ := eq156 X1 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq156 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq164 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | exact resolve eq160 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq369 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq164 (σ X0) X1
       grind)
    | exact superpose eq164 eq15
    | (have j1 := eq164 (σ X0) X1
       grind)
    | exact resolve eq15 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq391 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq406 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq369 (τ X1) X0
       grind)
    | exact superpose eq369 eq18
    | (have j1 := eq369 (τ X1) X0
       grind)
    | exact resolve eq18 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq999 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq406
    | exact resolve eq406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq1046 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq999 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq999
    | (have j0 := eq999 X0 X1
       grind)
    | exact resolve eq999 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq4200 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq391 x y
       grind)
    | exact superpose eq391 eq16
    | (have j1 := eq391 x y
       grind)
    | exact resolve eq16 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4225 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq4261 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4200
       have i₂ := eq1046 y x
       grind)
    | exact superpose eq1046 eq4200
    | (have j1 := eq1046 y x
       grind)
    | (have r₁ := eq4200
       have r₂ := eq1046 y x
       grind)
    | exact resolve eq4200 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046 eq4200
  have eq4262 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4261
  have eq4387 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq4262
       grind)
    | exact superpose eq4262 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4262
       grind)
    | exact resolve eq13 eq4262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4392 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by grind
  clear eq4387
  have eq4402 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4225 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq4225
    | (have j0 := eq4225 (τ X0) (τ X1)
       grind)
    | exact resolve eq4225 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq4454 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4402 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4402
    | (have j0 := eq4402 X0 X1
       grind)
    | exact resolve eq4402 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4402
  have eq4475 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4454 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq4454
    | (have j0 := eq4454 X0 X1
       grind)
    | exact resolve eq4454 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4491 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4475 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4475
    | (have j0 := eq4475 X0 X1
       grind)
    | exact resolve eq4475 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475
  have eq4501 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4491 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4491
    | (have j0 := eq4491 X0 X1
       grind)
    | exact resolve eq4491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4491
  have eq4506 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4501 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq4501
    | (have j0 := eq4501 X0 X1
       grind)
    | exact resolve eq4501 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4501
  have eq61913 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq4392
       grind)
    | exact superpose eq4392 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | (have r₁ := eq78 x (σ y)
       have r₂ := eq4392
       grind)
    | exact resolve eq78 eq4392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq61914 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq79 y (σ x)
       have i₂ := eq4392
       grind)
    | exact superpose eq4392 eq79
    | exact resolve eq79 eq4392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq61944 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by grind
  clear eq61913
  have eq61948 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq61914
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq61914
    | exact resolve eq61914 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61914
  have eq61949 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq61944
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq61944
    | exact resolve eq61944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61944
  have eq61953 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq61949
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq61949
    | exact resolve eq61949 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq61949
  have eq61955 : (k x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq61953
       have r₂ := eq61948
       grind)
    | exact resolve eq61953 eq61948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61948 eq61953
  have eq62446 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq61955
       have i₂ := eq369 y x
       grind)
    | exact superpose eq369 eq61955
    | (have j1 := eq369 y x
       grind)
    | exact resolve eq61955 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq62475 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4225 x y
       have i₂ := eq61955
       grind)
    | exact superpose eq61955 eq4225
    | (have j0 := eq4225 x y
       grind)
    | (have r₁ := eq4225 x y
       have r₂ := eq61955
       grind)
    | exact resolve eq4225 eq61955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61955
  have eq62522 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq62475
  have eq62529 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq62446
  have eq62532 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have j1 := eq4225 x y
       grind)
    | (have r₁ := eq62522
       have r₂ := eq4225 x y
       grind)
    | exact resolve eq62522 eq4225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62522
  have eq62541 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62532
       grind)
    | exact superpose eq62532 eq16
    | exact resolve eq16 eq62532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62532
  have eq64237 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq62541
       have i₂ := eq62529
       grind)
    | exact superpose eq62529 eq62541
    | (have r₁ := eq62541
       have r₂ := eq62529
       grind)
    | exact resolve eq62541 eq62529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62529
  have eq64251 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq64237
  have eq64252 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq64251
  have eq64262 : (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq64252
       have r₂ := eq62541
       grind)
    | exact resolve eq64252 eq62541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62541 eq64252
  have eq64271 : ∀ X0 : G, (M.op x x) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq64262
       grind)
    | exact superpose eq64262 eq12
    | (have j0 := eq12 X0 y
       grind)
    | exact resolve eq12 eq64262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65246 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq64271 x
       have i₂ := eq4262
       grind)
    | exact superpose eq4262 eq64271
    | (have r₁ := eq64271 x
       have r₂ := eq4262
       grind)
    | exact resolve eq64271 eq4262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4262 eq64271
  have eq65251 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq65246
  have eq65934 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq79 y (σ x)
       have i₂ := eq65251
       grind)
    | exact superpose eq65251 eq79
    | exact resolve eq79 eq65251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65251
  have eq65968 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq65934
       have i₂ := eq64262
       grind)
    | exact superpose eq64262 eq65934
    | exact resolve eq65934 eq64262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65934
  have eq65969 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq65968
  have eq65974 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq65969
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq65969
    | exact resolve eq65969 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65969
  have eq66753 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4225 x y
       have i₂ := eq65974
       grind)
    | exact superpose eq65974 eq4225
    | (have j0 := eq4225 x y
       grind)
    | (have r₁ := eq4225 x y
       have r₂ := eq65974
       grind)
    | exact resolve eq4225 eq65974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65974
  have eq66800 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq66753
  have eq66810 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq4225 x y
       grind)
    | (have r₁ := eq66800
       have r₂ := eq4225 x y
       grind)
    | exact resolve eq66800 eq4225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225 eq66800
  have eq67561 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66810
       grind)
    | exact superpose eq66810 eq16
    | exact resolve eq16 eq66810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67563 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq79 y (σ x)
       have i₂ := eq66810
       grind)
    | exact superpose eq66810 eq79
    | exact resolve eq79 eq66810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq66810
  have eq67597 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq67563
       have i₂ := eq64262
       grind)
    | exact superpose eq64262 eq67563
    | exact resolve eq67563 eq64262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64262 eq67563
  have eq67598 : (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq67597
  have eq67603 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67598
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq67598
    | exact resolve eq67598 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67598
  have eq68392 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq67603
       grind)
    | exact superpose eq67603 eq10
    | exact resolve eq10 eq67603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67603
  have eq68556 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq68392
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq68392
    | exact resolve eq68392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68392
  have eq68588 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4506 x y
       have i₂ := eq68556
       grind)
    | exact superpose eq68556 eq4506
    | (have j0 := eq4506 x y
       grind)
    | (have r₁ := eq4506 x y
       have r₂ := eq68556
       grind)
    | exact resolve eq4506 eq68556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4506 eq68556
  have eq68631 : (M.op x y) = (M.op x x) := by grind
  clear eq68588
  have eq69407 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq67561
       have i₂ := eq68631
       grind)
    | exact superpose eq68631 eq67561
    | exact resolve eq67561 eq68631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67561 eq68631
  have eq69419 : False := by grind
  exact eq69419

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq427 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq436 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq436 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq436 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq436 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq447 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq427 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq427 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq427 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq527 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq447 X0 X1
       grind)
    | exact superpose eq447 eq9
    | (have j1 := eq447 X0 X1
       grind)
    | exact resolve eq9 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq531 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq527 X0 X1
       have j1 := eq438 X1 X0
       grind)
    | (have r₁ := eq527 X1 X1
       have r₂ := eq438 X0 X1
       grind)
    | exact resolve eq527 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq527
  have eq548 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq531 (σ X1) (σ X0)
       grind)
    | exact superpose eq531 eq15
    | exact resolve eq15 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq531 X1 X0
       grind)
    | exact superpose eq531 eq548
    | exact resolve eq548 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq548
  have eq813 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq575 x y
       grind)
    | exact superpose eq575 eq16
    | (have r₁ := eq16
       have r₂ := eq575 x y
       grind)
    | exact resolve eq16 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq830 : False := by grind
  exact eq830

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq396 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq413 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq396
    | (have j0 := eq396 X0 X1
       grind)
    | exact resolve eq396 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq927 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq413 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq413
    | exact resolve eq413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq963 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq927 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq927
    | (have j0 := eq927 X0 X1
       grind)
    | exact resolve eq927 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq927
  have eq965 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq963 X0 X1
       have j1 := eq93 X1 X0
       grind)
    | (have r₁ := eq963 X1 X0
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq963 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq963 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq963
  have eq967 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq965 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq965
    | exact resolve eq965 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq965 (σ X0) X1
       grind)
    | exact superpose eq965 eq15
    | (have j1 := eq965 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1024 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq967 (τ X1) X0
       grind)
    | exact superpose eq967 eq19
    | (have j1 := eq967 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq967
  have eq1151 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1024 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1024
    | exact resolve eq1024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1191 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1151 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1151
    | (have j0 := eq1151 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1151 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1382 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq985 x y
       grind)
    | exact superpose eq985 eq16
    | (have j1 := eq985 x y
       grind)
    | exact resolve eq16 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1397 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1382
       have i₂ := eq1191 y x
       grind)
    | exact superpose eq1191 eq1382
    | (have j1 := eq1191 (σ x) (σ y)
       grind)
    | (have r₁ := eq1382
       have r₂ := eq1191 y x
       grind)
    | (have r₁ := eq1382
       have r₂ := eq1191 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1382
       have r₂ := eq1191 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1382 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191 eq1382
  have eq1398 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1397
  have eq1401 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq16
    | exact resolve eq16 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1402 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1401
       have r₂ := eq77 x
       grind)
    | exact resolve eq1401 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1403 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1402
       grind)
    | exact superpose eq1402 eq16
    | exact resolve eq16 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1404 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1402
       grind)
    | exact superpose eq1402 eq10
    | exact resolve eq10 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1448 : x = y := by
    first
    | (have i₁ := eq1404
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1404
    | exact resolve eq1404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1449 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1403
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq1403
    | exact resolve eq1403 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1403
  have eq1450 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1449
       have i₂ := eq1448
       grind)
    | exact superpose eq1448 eq1449
    | exact resolve eq1449 eq1448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448 eq1449
  have eq1451 : False := by grind
  exact eq1451
