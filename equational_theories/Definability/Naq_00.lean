import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation101`: `x = x ◇ ((x ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pxy_pyx_pxy_Equation101 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law101 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law101.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq25 (σ X0)
       grind)
    | exact superpose eq25 eq15
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq27
    | exact resolve eq27 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq27
  have eq62 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq67
    | (have j0 := eq67 X0 X1
       grind)
    | exact resolve eq67 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq67
  have eq117 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq72 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq72 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq13 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq124 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq129 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq124 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq124 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq141 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq129 X0 X1
       have j1 := eq62 X1 (σ X0)
       grind)
    | (have r₁ := eq129 X0 X0
       have r₂ := eq62 X0 (σ X0)
       grind)
    | exact resolve eq129 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq129
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq141
    | (have j0 := eq141 X0 X1
       grind)
    | exact resolve eq141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq155 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq150
    | exact resolve eq150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq150 x y
       grind)
    | exact superpose eq150 eq16
    | exact resolve eq16 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq478 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq155 X0 (τ X1)
       grind)
    | exact superpose eq155 eq20
    | exact resolve eq20 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq155
  have eq507 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq478
    | exact resolve eq478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq523 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq507
    | exact resolve eq507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq701 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq166
       have i₂ := eq523 x y
       grind)
    | exact superpose eq523 eq166
    | exact resolve eq166 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq523
  have eq702 : False := by grind
  exact eq702

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pxx_pyx_pxy_Equation1027 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq20 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op X0 x)
       have i₂ := eq20 X0 x
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq95 (σ X0) (σ X1)
       grind)
    | exact superpose eq95 eq15
    | (have j1 := eq95 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq95 (τ X0) X1
       grind)
    | exact superpose eq95 eq17
    | (have j1 := eq95 (τ X0) X1
       grind)
    | exact resolve eq17 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq95
  have eq496 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137
    | exact resolve eq137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq533 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq496
    | (have j0 := eq496 X0 X1
       grind)
    | exact resolve eq496 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq755 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq132 x y
       grind)
    | exact superpose eq132 eq16
    | (have j1 := eq132 x y
       grind)
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq3013 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq755
       have i₂ := eq533 x y
       grind)
    | exact superpose eq533 eq755
    | (have j1 := eq533 (σ x) (σ y)
       grind)
    | (have r₁ := eq755
       have r₂ := eq533 x y
       grind)
    | exact resolve eq755 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq755
  have eq3014 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3013
  have eq3018 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20 x y
       have i₂ := eq3014
       grind)
    | exact superpose eq3014 eq20
    | exact resolve eq20 eq3014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3048 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3014
       have i₂ := eq3018
       grind)
    | exact superpose eq3018 eq3014
    | exact resolve eq3014 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014 eq3018
  have eq3072 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3048
  have eq3132 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3072
       grind)
    | exact superpose eq3072 eq16
    | exact resolve eq16 eq3072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3072
  have eq3133 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3132
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq3132
    | exact resolve eq3132 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3132
  have eq3134 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3133
       have r₂ := eq23 (σ x)
       grind)
    | exact resolve eq3133 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq3137 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3134
       grind)
    | exact superpose eq3134 eq16
    | exact resolve eq16 eq3134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3141 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20 (σ x) (σ y)
       have i₂ := eq3134
       grind)
    | exact superpose eq3134 eq20
    | exact resolve eq20 eq3134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3386 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3134
       have i₂ := eq3141
       grind)
    | exact superpose eq3141 eq3134
    | exact resolve eq3134 eq3141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3134 eq3141
  have eq3635 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3386
       grind)
    | exact superpose eq3386 eq10
    | exact resolve eq10 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq3680 : x = y := by
    first
    | (have i₁ := eq3635
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3635
    | exact resolve eq3635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3635
  have eq3687 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3137
       have i₂ := eq3680
       grind)
    | exact superpose eq3680 eq3137
    | exact resolve eq3137 eq3680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3137 eq3680
  have eq3691 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3687
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq3687
    | exact resolve eq3687 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3687
  have eq3692 : False := by grind
  exact eq3692

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_pxx_pxy_Equation1043 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1043 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
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
  clear eq25 eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq352 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq53 X0 X1 X3 X4
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq353
    | exact resolve eq353 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq356 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq352 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq352
    | exact resolve eq352 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq457 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq458 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq3020 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq356 X0 X0 x
       grind)
    | exact superpose eq356 eq53
    | exact resolve eq53 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3042 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq356 X0 X0 X0
       have i₂ := eq3020 X0
       grind)
    | exact superpose eq3020 eq356
    | exact resolve eq356 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq3020
  have eq3086 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3091 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 (M.op X0 X0)
       have i₂ := eq3042 X0
       grind)
    | exact superpose eq3042 eq14
    | exact resolve eq14 eq3042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3094 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3091 X0 X1
       have i₂ := eq355 (M.op X0 X0) X1
       grind)
    | exact superpose eq355 eq3091
    | exact resolve eq3091 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq3091
  have eq3098 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3086 X0
       have i₂ := eq3042 X0
       grind)
    | exact superpose eq3042 eq3086
    | exact resolve eq3086 eq3042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3160 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq458 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq458
    | (have j0 := eq458 (τ X0)
       grind)
    | exact resolve eq458 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3169 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3160 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3160
    | (have j0 := eq3160 X0
       grind)
    | exact resolve eq3160 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3160
  have eq3175 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3169 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3169
    | (have j0 := eq3169 X0
       grind)
    | exact resolve eq3169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq15541 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq3094 X0 X1
       grind)
    | exact superpose eq3094 eq14
    | exact resolve eq14 eq3094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15584 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15541 X0 X1
       have i₂ := eq3042 X0
       grind)
    | exact superpose eq3042 eq15541
    | exact resolve eq15541 eq3042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15541
  have eq15802 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3094 X1 X0
       have i₂ := eq15584 X1 X0
       grind)
    | exact superpose eq15584 eq3094
    | exact resolve eq3094 eq15584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3094 eq15584
  have eq18209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq18210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18209
    | exact resolve eq18209 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18221 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18210
       have r₂ := eq28
       grind)
    | exact resolve eq18210 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18210
  have eq18237 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18221 eq3042
    | exact resolve eq3042 eq18221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18221
  have eq18260 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq18237
  have eq18276 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18260 eq3098
    | exact resolve eq3098 eq18260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18260
  have eq18318 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18276 eq50
    | exact resolve eq50 eq18276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq18276
  have eq18353 : x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq18318
    | exact resolve eq18318 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18318
  have eq18356 : x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3175 x
       grind)
    | (have r₁ := eq18353
       have r₂ := eq3175 x
       grind)
    | exact resolve eq18353 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175 eq18353
  have eq18371 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3042 y
       have i₂ := eq18356
       grind)
    | exact superpose eq18356 eq3042
    | exact resolve eq3042 eq18356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042 eq18356
  have eq18394 : x = (M.op x x) := by grind
  clear eq18371
  have eq18410 : x = (k x x) := by
    first
    | (have i₁ := eq3098 x
       have i₂ := eq18394
       grind)
    | exact superpose eq18394 eq3098
    | exact resolve eq3098 eq18394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098
  have eq18412 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq15802 X0 x
       have i₂ := eq18394
       grind)
    | exact superpose eq18394 eq15802
    | exact resolve eq15802 eq18394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18394
  have eq18463 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq458 x
       have i₂ := eq18410
       grind)
    | exact superpose eq18410 eq458
    | (have j0 := eq458 x
       grind)
    | exact resolve eq458 eq18410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq18410
  have eq18472 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq18463
  have eq18480 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18472
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18472
    | exact resolve eq18472 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18472
  have eq18590 : x = (M.op x y) := by
    first
    | (have i₁ := eq18412 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18412
    | (have j0 := eq18412 y
       grind)
    | exact resolve eq18412 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq18412
  have eq18745 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18590 eq21
    | exact resolve eq21 eq18590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18590
  have eq18895 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18745
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18745
    | exact resolve eq18745 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18745
  have eq19340 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18895 eq27
    | exact resolve eq27 eq18895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq19474 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq18895 eq18480
    | exact resolve eq18480 eq18895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18480 eq18895
  have eq20041 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq19474 eq15802
    | exact resolve eq15802 eq19474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15802 eq19474
  have eq21631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20041 eq19340
    | exact resolve eq19340 eq20041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19340 eq20041
  have eq21632 : False := by grind
  exact eq21632

/-- `Equation1052`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pxy_Equation1052 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1052 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1052.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X1)) = X0 := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq177 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq630 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq633 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq638 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq627
       grind)
    | exact superpose eq627 eq41
    | exact resolve eq41 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq639 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq638
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq638
    | exact resolve eq638 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq641 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq639
    | exact resolve eq639 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq641 eq630
    | exact resolve eq630 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq641
  have eq658 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq651
       have r₂ := eq27
       grind)
    | exact resolve eq651 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq666 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq658 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq658
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq658
       grind)
    | exact resolve eq13 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq678 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq667 eq658
    | exact resolve eq658 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq667
  have eq691 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq678
  have eq698 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq691 eq153
    | exact resolve eq153 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq691
  have eq701 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq698
    | exact resolve eq698 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq698
  have eq704 : y = (M.op y y) := by
    first
    | (have j1 := eq633 y
       grind)
    | (have r₁ := eq701
       have r₂ := eq633 y
       grind)
    | exact resolve eq701 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq710 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 y X0
       have i₂ := eq704
       grind)
    | exact superpose eq704 eq177
    | exact resolve eq177 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq704
       grind)
    | exact superpose eq704 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq704
       grind)
    | exact resolve eq13 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq713 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq710 X0
       have i₂ := eq704
       grind)
    | exact superpose eq704 eq710
    | exact resolve eq710 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq710
  have eq725 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq713 x
       grind)
    | exact superpose eq713 eq18
    | (have j1 := eq713 x
       grind)
    | exact resolve eq18 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq734 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq725
       grind)
    | exact superpose eq725 eq22
    | exact resolve eq22 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq725
  have eq847 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq734 eq20
    | exact resolve eq20 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq734
  have eq927 : y = (k y y) := by
    first
    | (have i₁ := eq713 y
       have i₂ := eq712 y
       grind)
    | exact superpose eq712 eq713
    | exact resolve eq713 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq713
  have eq945 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq41
    | exact resolve eq41 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq927
  have eq948 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq945
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq945
    | exact resolve eq945 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq945
  have eq953 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq948 eq633
    | (have j0 := eq633 (σ y)
       grind)
    | (have r₁ := eq633 (σ y)
       have r₂ := eq948
       grind)
    | exact resolve eq633 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq948
  have eq954 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq953
  have eq963 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq954 eq177
    | exact resolve eq177 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq969 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq954 eq963
    | exact resolve eq963 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq963
  have eq986 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq969 eq26
    | (have j1 := eq969 (σ x)
       grind)
    | exact resolve eq26 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq969
  have eq999 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq986 eq27
    | exact resolve eq27 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq986
  have eq1000 : False := by grind
  exact eq1000

/-- `Equation1267`: `x = x ◇ (((y ◇ z) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation1267 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1267 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1267.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) = X0 := by
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
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 X0 (M.op (M.op (M.op X1 X2) X2) X1)
       have i₂ := eq16 (M.op X0 (M.op (M.op (M.op X1 X2) X2) X1)) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq177 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq186 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq179 X0 (M.op X0 X0)
       grind)
    | exact superpose eq179 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq179 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1187 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq1190 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1217 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq179 X0 (M.op X0 X0)
       grind)
    | exact superpose eq179 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq179 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq2369 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1187
       grind)
    | exact superpose eq1187 eq39
    | exact resolve eq39 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1187
  have eq2370 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2369
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2369
    | exact resolve eq2369 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq2372 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2370
    | exact resolve eq2370 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq9116 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = X0 ∨ (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq1233 X0 X1
       grind)
    | exact superpose eq1233 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq1233 X0 X0
       grind)
    | exact resolve eq11 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9172 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1233 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9176 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9116 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9116
  have eq9181 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9176 X0 X1
       have j1 := eq9172 X0 X1
       grind)
    | (have r₁ := eq9176 X0 X1
       have r₂ := eq9172 X0 X1
       grind)
    | exact resolve eq9176 eq9172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9172 eq9176
  have eq10081 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1233 x X0
       have i₂ := eq9181 X0 x
       grind)
    | (have i₁ := eq1233 X0 (M.op X0 X0)
       have i₂ := eq9181 (M.op X0 X0) x
       grind)
    | exact superpose eq9181 eq1233
    | (have j0 := eq1233 X0 X0
       have j1 := eq9181 X0 x
       grind)
    | exact resolve eq1233 eq9181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233 eq9181
  have eq10117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10081
  have eq10158 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10117 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq10117 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq10117 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10117
  have eq10331 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq10158 X0
       grind)
    | exact superpose eq10158 eq179
    | exact resolve eq179 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq10420 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10331 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq10331
    | exact resolve eq10331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10561 : ∀ X0 X1 : G, (k (σ (k X0 X0)) X1) = (M.op (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq189 (σ (k X0 X0)) X1
       have i₂ := eq10420 X0 (σ (k X0 X0))
       grind)
    | exact superpose eq10420 eq189
    | exact resolve eq189 eq10420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2372 eq1190
    | exact resolve eq1190 eq2372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq2372
  have eq34869 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq34860
       have r₂ := eq27
       grind)
    | exact resolve eq34860 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34860
  have eq34876 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34869
       have i₂ := eq10158 sF2
       grind)
    | exact superpose eq10158 eq34869
    | exact resolve eq34869 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34869
  have eq34881 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34876
       have i₂ := eq10158 sF3
       grind)
    | exact superpose eq10158 eq34876
    | exact resolve eq34876 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34876
  have eq34886 : x = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34881
       have i₂ := eq10158 x
       grind)
    | exact superpose eq10158 eq34881
    | exact resolve eq34881 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34881
  have eq34888 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x x) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq34886
       have i₂ := eq10158 y
       grind)
    | exact superpose eq10158 eq34886
    | exact resolve eq34886 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34886
  have eq34896 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (k x x) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq34888 eq152
    | exact resolve eq152 eq34888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq34888
  have eq35041 : y = (k y y) ∨ x = (k x x) ∨ y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq34896
    | exact resolve eq34896 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq34896
  have eq35042 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ y = (k y y) := by grind
  clear eq35041
  have eq35064 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq35042 eq141
    | exact resolve eq141 eq35042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq35042
  have eq35209 : x = (k x x) ∨ x = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq29 eq35064
    | exact resolve eq35064 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35064
  have eq35210 : y = (k y y) ∨ x = (k x x) := by grind
  clear eq35209
  have eq35236 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq10331 y X0
       have i₂ := eq35210
       grind)
    | exact superpose eq35210 eq10331
    | exact resolve eq10331 eq35210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35249 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq10420 y X0
       have i₂ := eq35210
       grind)
    | exact superpose eq35210 eq10420
    | exact resolve eq10420 eq35210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10420 eq35210
  have eq35373 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq35249 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35249
    | (have j0 := eq35249 X0
       grind)
    | exact resolve eq35249 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35249
  have eq35404 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10331 x X0
       have i₂ := eq35236 X1
       grind)
    | exact superpose eq35236 eq10331
    | (have j1 := eq35236 X1
       grind)
    | exact resolve eq10331 eq35236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35236
  have eq35740 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10331 x X0
       have i₂ := eq35373 X1
       grind)
    | exact superpose eq35373 eq10331
    | (have j1 := eq35373 X1
       grind)
    | exact resolve eq10331 eq35373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10331 eq35373
  have eq35986 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq35404 X0 x
       grind)
    | exact superpose eq35404 eq18
    | (have j1 := eq35404 X0 x
       grind)
    | exact resolve eq18 eq35404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35404
  have eq36119 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq189 x x
       have i₂ := eq35986 x
       grind)
    | exact superpose eq35986 eq189
    | exact resolve eq189 eq35986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36132 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10158 x
       have i₂ := eq35986 x
       grind)
    | exact superpose eq35986 eq10158
    | exact resolve eq10158 eq35986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35986
  have eq36320 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10561 x x
       have i₂ := eq36132
       grind)
    | exact superpose eq36132 eq10561
    | exact resolve eq10561 eq36132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36132
  have eq36438 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq36320 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36320
    | (have j0 := eq36320 X0
       grind)
    | exact resolve eq36320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36320
  have eq37718 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq35740 (M.op sF2 sF3) x
       grind)
    | exact superpose eq35740 eq26
    | (have j1 := eq35740 X0 (σ x)
       grind)
    | exact resolve eq26 eq35740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35740
  have eq37868 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq189 x x
       have i₂ := eq37718 x
       grind)
    | exact superpose eq37718 eq189
    | exact resolve eq189 eq37718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq37881 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10158 x
       have i₂ := eq37718 x
       grind)
    | exact superpose eq37718 eq10158
    | exact resolve eq10158 eq37718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10158 eq37718
  have eq38069 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10561 x x
       have i₂ := eq37881
       grind)
    | exact superpose eq37881 eq10561
    | exact resolve eq10561 eq37881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10561 eq37881
  have eq38187 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq38069 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38069
    | (have j0 := eq38069 X0
       grind)
    | exact resolve eq38069 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38069
  have eq39857 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36119 y
       grind)
    | exact superpose eq36119 eq18
    | (have j1 := eq36119 y
       grind)
    | exact resolve eq18 eq36119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36119
  have eq40081 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq39857
       grind)
    | exact superpose eq39857 eq40
    | exact resolve eq40 eq39857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39857
  have eq40083 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40081
    | exact resolve eq40081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40081
  have eq40087 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq40083
    | exact resolve eq40083 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40083
  have eq42182 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36438 eq26
    | (have j1 := eq36438 (σ y)
       grind)
    | exact resolve eq26 eq36438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36438
  have eq42351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40087 eq42182
    | exact resolve eq42182 eq40087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40087 eq42182
  have eq42406 : x = (M.op x y) := by
    first
    | (have r₁ := eq42351
       have r₂ := eq27
       grind)
    | exact resolve eq42351 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42351
  have eq42424 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq42406
       grind)
    | exact superpose eq42406 eq22
    | exact resolve eq22 eq42406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq42482 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq42424 eq20
    | exact resolve eq20 eq42424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42424
  have eq46527 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq37868 y
       grind)
    | exact superpose eq37868 eq18
    | (have j1 := eq37868 y
       grind)
    | exact resolve eq18 eq37868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq37868
  have eq46723 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46527
       have i₂ := eq42406
       grind)
    | exact superpose eq42406 eq46527
    | exact resolve eq46527 eq42406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42406 eq46527
  have eq46888 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46723 eq40
    | exact resolve eq40 eq46723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq46723
  have eq46890 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq46888
    | exact resolve eq46888 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq46888
  have eq46895 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42482 eq46890
    | exact resolve eq46890 eq42482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46890
  have eq48242 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38187 eq26
    | (have j1 := eq38187 (σ y)
       grind)
    | exact resolve eq26 eq38187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq38187
  have eq48428 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46895 eq48242
    | exact resolve eq48242 eq46895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46895 eq48242
  have eq48429 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq48428
  have eq48493 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq48429 eq27
    | exact resolve eq27 eq48429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq48429
  have eq48532 : False := by grind
  exact eq48532

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyx_pyx_pxx_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq39 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq47
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq55
  have eq138 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq142 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       have j1 := eq57 X1 X0
       grind)
    | (have r₁ := eq138 X1 X0
       have r₂ := eq57 X0 X1
       grind)
    | (have r₁ := eq138 X0 X0
       have r₂ := eq57 X0 X0
       grind)
    | exact resolve eq138 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq138
  have eq290 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq142 (σ X1) (σ X0)
       grind)
    | exact superpose eq142 eq15
    | exact resolve eq15 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq142 X1 X0
       grind)
    | exact superpose eq142 eq290
    | exact resolve eq290 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq290
  have eq299 : False := by grind
  exact eq299

/-- `Equation1577`: `x = (y ◇ z) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pyx_pxy_Equation1577 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1577 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1577.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq27 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq748 : ∀ X0 X1 : G, (τ X1) ≠ X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq789 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq748 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq748
    | (have j0 := eq748 X1 X1
       grind)
    | (have r₁ := eq748 X0 (σ X0)
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq748 (τ (σ (τ X1))) X1
       have r₂ := eq10 (τ X1)
       grind)
    | exact resolve eq748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq801 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq789 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq789
    | (have j0 := eq789 X0 X1
       grind)
    | (have r₁ := eq789 (σ (k X0 X1)) (k (σ X0) (σ X1))
       have r₂ := eq15 X0 X1
       grind)
    | (have r₁ := eq789 (k (σ X0) (σ X1)) (σ (k X0 X1))
       have r₂ := eq15 X0 X1
       grind)
    | exact resolve eq789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq802 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq801 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq821 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq802 X0
       grind)
    | exact superpose eq802 eq10
    | (have j1 := eq802 X0
       grind)
    | exact resolve eq10 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq854 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq821 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq821
    | (have j0 := eq821 X0
       grind)
    | exact resolve eq821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq870 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq854 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq854 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq854 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq917 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq870 (σ X0)
       grind)
    | exact superpose eq870 eq15
    | exact resolve eq15 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq870 (τ X0)
       grind)
    | exact superpose eq870 eq35
    | exact resolve eq35 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq944 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq923 X0
       have i₂ := eq870 X0
       grind)
    | exact superpose eq870 eq923
    | exact resolve eq923 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq950 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq917 X0
       have i₂ := eq870 X0
       grind)
    | exact superpose eq870 eq917
    | exact resolve eq917 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq917
  have eq1130 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq9
    | exact resolve eq9 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (M.op (τ X0) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq9
    | exact resolve eq9 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (τ X0)
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1135 X0 X1
       have j1 := eq1137 X0 X1
       grind)
    | (have r₁ := eq1135 X0 X1
       have r₂ := eq1137 X0 X1
       grind)
    | (have r₁ := eq1135 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq1137 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq1135 X0 (τ X0)
       have r₂ := eq1137 X0 X1
       grind)
    | exact resolve eq1135 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq1137
  have eq1176 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq950 X0
       grind)
    | exact superpose eq950 eq9
    | exact resolve eq9 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1177 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq950 X0
       grind)
    | exact superpose eq950 eq9
    | exact resolve eq9 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (σ X0)
       have i₂ := eq950 X0
       grind)
    | exact superpose eq950 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq950 X0
       grind)
    | exact superpose eq950 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1185 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1181 X0 X1
       have j1 := eq1183 X0 X1
       grind)
    | (have r₁ := eq1181 X0 X1
       have r₂ := eq1183 X0 X1
       grind)
    | (have r₁ := eq1181 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq1183 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq1181 X0 (σ X0)
       have r₂ := eq1183 X0 X1
       grind)
    | exact resolve eq1181 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq1183
  have eq1217 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1130 X0 (τ (M.op X0 X0))
       have i₂ := eq944 (M.op X0 X0)
       grind)
    | exact superpose eq944 eq1130
    | exact resolve eq1130 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (M.op X1 (τ X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ (M.op X0 X0)) (M.op X1 (τ X0)) X1
       have i₂ := eq1130 X0 X1
       grind)
    | exact superpose eq1130 eq9
    | exact resolve eq9 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1262 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (M.op (M.op (τ (M.op X1 X1)) (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X1) X0) (τ (M.op X1 X1)) (τ X1)
       have i₂ := eq1131 X1 X0
       grind)
    | exact superpose eq1131 eq9
    | exact resolve eq9 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq1266 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1217 X0
       have i₂ := eq1262 (τ (M.op (M.op X0 X0) (M.op X0 X0))) X0
       grind)
    | exact superpose eq1262 eq1217
    | exact resolve eq1217 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1312 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1176 X0 (σ (M.op X0 X0))
       have i₂ := eq950 (M.op X0 X0)
       grind)
    | exact superpose eq950 eq1176
    | exact resolve eq1176 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1364 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X1 X1)) (σ X1)) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (σ X1) X0) (σ (M.op X1 X1)) (σ X1)
       have i₂ := eq1177 X1 X0
       grind)
    | exact superpose eq1177 eq9
    | exact resolve eq9 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1369 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1312 X0
       have i₂ := eq1364 (σ (M.op (M.op X0 X0) (M.op X0 X0))) X0
       grind)
    | exact superpose eq1364 eq1312
    | exact resolve eq1312 eq1364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1402 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1218 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1218
    | exact resolve eq1218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1416 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1402 X0 X1
       have i₂ := eq950 X0
       grind)
    | exact superpose eq950 eq1402
    | exact resolve eq1402 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1426 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1416 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1416
    | exact resolve eq1416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq1472 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (τ (M.op (σ X0) (σ X0))) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1262 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1262
    | exact resolve eq1262 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1523 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (τ (σ (M.op X0 X0))) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1472 X0 X1
       have i₂ := eq950 X0
       grind)
    | exact superpose eq950 eq1472
    | exact resolve eq1472 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1529 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1523 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1523
    | exact resolve eq1523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1546 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq1529 X0 (M.op (M.op X0 X0) (M.op X0 X1))
       grind)
    | exact superpose eq1529 eq9
    | exact resolve eq9 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1602 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1546 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq1546 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq1546
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq1546 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1546 X1 (M.op (M.op X1 X1) (M.op X1 X0))
       have i₂ := eq1546 X1 X0
       grind)
    | exact superpose eq1546 eq1546
    | exact resolve eq1546 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1605 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1546 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq1546
    | exact resolve eq1546 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1623 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1 (M.op X1 X1)
       have i₂ := eq1546 X1 X0
       grind)
    | exact superpose eq1546 eq9
    | exact resolve eq9 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1625 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op X2 X0)) X1 X2
       have i₂ := eq1546 X2 X0
       grind)
    | exact superpose eq1546 eq9
    | exact resolve eq9 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1627 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op (M.op X1 X1) X1) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X1 (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op (M.op (M.op X1 X1) X1) X0))
       have i₂ := eq1546 (M.op (M.op X1 X1) X1) X0
       grind)
    | exact superpose eq1546 eq1529
    | exact resolve eq1529 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1634 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op (M.op X1 X1) X1) (M.op (M.op X1 X1) X1)) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1627 X0 X1
       have i₂ := eq1529 X1 X0
       grind)
    | exact superpose eq1529 eq1627
    | exact resolve eq1627 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq1649 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq1266 X0
       have i₂ := eq1604 X0 X0
       grind)
    | exact superpose eq1604 eq1266
    | exact resolve eq1266 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1654 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq1369 X0
       have i₂ := eq1604 X0 X0
       grind)
    | exact superpose eq1604 eq1369
    | exact resolve eq1369 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1664 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op X2 (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1625 X0 X1 X2
       have i₂ := eq1604 X0 X2
       grind)
    | exact superpose eq1604 eq1625
    | exact resolve eq1625 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq1666 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1546 X0 X1
       have i₂ := eq1604 X1 X0
       grind)
    | exact superpose eq1604 eq1546
    | exact resolve eq1546 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546 eq1604
  have eq1667 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1602 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1602 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1602 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1602 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1674 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (M.op (M.op X1 X1) X1)) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1634 X0 X1
       have i₂ := eq1529 X1 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq1529 eq1634
    | exact resolve eq1634 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq1698 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1666 (σ X0) X1
       have i₂ := eq950 X0
       grind)
    | exact superpose eq950 eq1666
    | exact resolve eq1666 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1699 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1666 (τ X0) X1
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq1666
    | exact resolve eq1666 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1775 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X1 (τ X0)
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq1623
    | exact resolve eq1623 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1974 : ∀ X0 X1 : G, (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0))) = (τ (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ (M.op X0 (M.op (M.op X0 X0) X0))) X1 (τ X0)
       have i₂ := eq1649 X0
       grind)
    | exact superpose eq1649 eq9
    | exact resolve eq9 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2353 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) = (τ (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1699 X0 (τ (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0))))
       have i₂ := eq1649 (M.op X0 X0)
       grind)
    | exact superpose eq1649 eq1699
    | exact resolve eq1699 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2375 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0)))) = (τ (M.op X0 (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2353 X0
       have i₂ := eq1605 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq1605 eq2353
    | exact resolve eq2353 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2848 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1140 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1140
    | (have j0 := eq1140 (σ X0) X1
       grind)
    | exact resolve eq1140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq2929 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2848 X0 X1
       have i₂ := eq950 X0
       grind)
    | exact superpose eq950 eq2848
    | (have j0 := eq2848 X0 X1
       grind)
    | exact resolve eq2848 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848
  have eq2936 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2929 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2929
    | (have j0 := eq2929 X0 X1
       grind)
    | exact resolve eq2929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq3119 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1185 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1185 X0 (σ X0)
       grind)
    | exact superpose eq1185 eq10
    | (have j1 := eq1185 X1 X0
       grind)
    | exact resolve eq10 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq3831 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3119 (σ X0) X1
       grind)
    | exact superpose eq3119 eq15
    | (have j1 := eq3119 (σ X0) X1
       grind)
    | exact resolve eq15 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3857 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3831 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3831
    | (have j0 := eq3831 X0 X1
       grind)
    | exact resolve eq3831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831
  have eq5070 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3857 x y
       grind)
    | exact superpose eq3857 eq16
    | (have j1 := eq3857 x y
       grind)
    | exact resolve eq16 eq3857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5254 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5070
       have i₂ := eq2936 y x
       grind)
    | exact superpose eq2936 eq5070
    | (have j1 := eq2936 y x
       grind)
    | exact resolve eq5070 eq2936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5070
  have eq5260 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq5254
  have eq5261 : x = (M.op y y) := by grind
  clear eq5260
  have eq5688 : ∀ X0 : G, (M.op (τ y) X0) = (M.op (M.op (τ x) (τ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1262 X0 y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq1262
    | exact resolve eq1262 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5689 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1364 X0 y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq1364
    | exact resolve eq1364 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5690 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1529 y X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq1529
    | exact resolve eq1529 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq5691 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y x) X0) := by
    intro X0
    first
    | (have i₁ := eq1623 X0 y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq1623
    | exact resolve eq1623 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5693 : (σ y) = (M.op (σ y) (σ (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq1654 y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq1654
    | exact resolve eq1654 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5694 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1666 y X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq1666
    | exact resolve eq1666 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5696 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1698 y X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq1698
    | exact resolve eq1698 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5697 : ∀ X0 : G, (M.op (τ y) (M.op (τ y) (M.op (τ x) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1699 y X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq1699
    | exact resolve eq1699 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5703 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq2936 y X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq2936
    | (have j0 := eq2936 y X0
       grind)
    | exact resolve eq2936 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5704 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq3119 X0 y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq3119
    | (have j0 := eq3119 X0 y
       grind)
    | exact resolve eq3119 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq5708 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq3857 X0 y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq3857
    | (have j0 := eq3857 X0 y
       grind)
    | exact resolve eq3857 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3857
  have eq5713 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq9
    | exact resolve eq9 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5714 : ∀ X0 : G, (M.op x (M.op y (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq9
    | exact resolve eq9 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5715 : y = (M.op y (M.op (M.op y y) x)) := by
    first
    | (have i₁ := eq5713 x
       have i₂ := eq1664 x x y
       grind)
    | exact superpose eq1664 eq5713
    | exact resolve eq5713 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5713
  have eq5722 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq5715
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq5715
    | exact resolve eq5715 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5715
  have eq5736 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y y) (M.op x x)) := by
    first
    | (have i₁ := eq1426 (M.op x x) y
       have i₂ := eq5722
       grind)
    | exact superpose eq5722 eq1426
    | exact resolve eq1426 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5737 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x x) X0 y
       have i₂ := eq5722
       grind)
    | exact superpose eq5722 eq9
    | exact resolve eq9 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5738 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x x) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y (M.op x x)
       have i₂ := eq5722
       grind)
    | exact superpose eq5722 eq9
    | exact resolve eq9 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5722
  have eq5739 : (M.op y (M.op (M.op y y) y)) = (M.op x x) := by
    first
    | (have i₁ := eq5737 x
       have i₂ := eq1664 y x y
       grind)
    | exact superpose eq1664 eq5737
    | exact resolve eq5737 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5737
  have eq5740 : (M.op (M.op x x) (M.op x x)) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq5736
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq5736
    | exact resolve eq5736 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5736
  have eq5742 : (M.op y (M.op x y)) = (M.op x x) := by
    first
    | (have i₁ := eq5739
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq5739
    | exact resolve eq5739 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5739
  have eq5743 : (M.op x (M.op x x)) = (M.op x (M.op (M.op x x) x)) := by
    first
    | (have i₁ := eq5740
       have i₂ := eq1664 x x x
       grind)
    | exact superpose eq1664 eq5740
    | exact resolve eq5740 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740
  have eq5745 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq5693
       have i₂ := eq5742
       grind)
    | exact superpose eq5742 eq5693
    | exact resolve eq5693 eq5742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5693
  have eq5785 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (M.op (M.op y (M.op x y)) (M.op x y))))) := by
    first
    | (have i₁ := eq1654 (M.op x y)
       have i₂ := eq5690 (M.op x y)
       grind)
    | exact superpose eq5690 eq1654
    | exact resolve eq1654 eq5690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5805 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X1 (M.op y X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op x y)
       have i₂ := eq5690 X0
       grind)
    | exact superpose eq5690 eq9
    | exact resolve eq9 eq5690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5850 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op (M.op y (M.op x y)) (M.op x y))))) := by
    first
    | (have i₁ := eq5785
       have i₂ := eq5690 (M.op (M.op y (M.op x y)) (M.op x y))
       grind)
    | exact superpose eq5690 eq5785
    | exact resolve eq5785 eq5690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5785
  have eq5890 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op (M.op x x) (M.op x y))))) := by
    first
    | (have i₁ := eq5850
       have i₂ := eq5742
       grind)
    | exact superpose eq5742 eq5850
    | exact resolve eq5850 eq5742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5742 eq5850
  have eq5910 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op x (M.op (M.op x x) y))))) := by
    first
    | (have i₁ := eq5890
       have i₂ := eq1664 y x x
       grind)
    | exact superpose eq1664 eq5890
    | exact resolve eq5890 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5890
  have eq5980 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y x)) (M.op X1 (M.op y X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op y x)
       have i₂ := eq5691 X0
       grind)
    | exact superpose eq5691 eq9
    | exact resolve eq9 eq5691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5691
  have eq6053 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq5694 (M.op x (M.op (M.op x x) X0))
       have i₂ := eq1666 x X0
       grind)
    | exact superpose eq1666 eq5694
    | exact resolve eq5694 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6064 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op (M.op y (M.op x X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 y (M.op y (M.op x X0))
       have i₂ := eq5694 X0
       grind)
    | exact superpose eq5694 eq9
    | exact resolve eq9 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6066 : (M.op x (M.op x x)) = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq5743
       have i₂ := eq6053 x
       grind)
    | exact superpose eq6053 eq5743
    | exact resolve eq5743 eq6053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5743
  have eq6069 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op y (M.op y y))))) := by
    first
    | (have i₁ := eq5910
       have i₂ := eq6053 y
       grind)
    | exact superpose eq6053 eq5910
    | exact resolve eq5910 eq6053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5910
  have eq6072 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op y (M.op y x)))) := by
    first
    | (have i₁ := eq6069
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq6069
    | exact resolve eq6069 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6069
  have eq6109 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x (M.op x x)))) := by
    first
    | (have i₁ := eq6072
       have i₂ := eq6066
       grind)
    | exact superpose eq6066 eq6072
    | exact resolve eq6072 eq6066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6072
  have eq6121 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq5714 y
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq5714
    | exact resolve eq5714 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6123 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq5714 (M.op y (M.op x X0))
       have i₂ := eq5694 X0
       grind)
    | exact superpose eq5694 eq5714
    | exact resolve eq5714 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5694
  have eq6129 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq5714 y
       have i₂ := eq2936 y X0
       grind)
    | (have i₁ := eq5714 X0
       have i₂ := eq2936 X0 (M.op y X0)
       grind)
    | exact superpose eq2936 eq5714
    | (have j1 := eq2936 y X0
       grind)
    | exact resolve eq5714 eq2936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936
  have eq6145 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op (M.op y (M.op y X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x (M.op y (M.op y X0))
       have i₂ := eq5714 X0
       grind)
    | exact superpose eq5714 eq9
    | exact resolve eq9 eq5714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6157 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op (M.op x (M.op y X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6064 X0 X1
       have i₂ := eq6123 X0
       grind)
    | exact superpose eq6123 eq6064
    | exact resolve eq6064 eq6123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6064
  have eq6202 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq5703 (τ X0)
       grind)
    | exact superpose eq5703 eq19
    | (have j1 := eq5703 (τ X0)
       grind)
    | exact resolve eq19 eq5703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5703
  have eq6298 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (M.op (σ y) (σ y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq1426 (σ (M.op x x)) (σ y)
       have i₂ := eq5745
       grind)
    | exact superpose eq5745 eq1426
    | exact resolve eq1426 eq5745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5745
  have eq6302 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op y y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq6298
       have i₂ := eq950 y
       grind)
    | exact superpose eq950 eq6298
    | exact resolve eq6298 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6298
  have eq6310 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq6302
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq6302
    | exact resolve eq6302 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6302
  have eq6316 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq6310
       have i₂ := eq950 (M.op x x)
       grind)
    | exact superpose eq950 eq6310
    | exact resolve eq6310 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6310
  have eq6320 : (σ (M.op x (M.op (M.op x x) x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq6316
       have i₂ := eq1664 x x x
       grind)
    | exact superpose eq1664 eq6316
    | exact resolve eq6316 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6316
  have eq6321 : (σ (M.op y (M.op y x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq6320
       have i₂ := eq6053 x
       grind)
    | exact superpose eq6053 eq6320
    | exact resolve eq6320 eq6053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6053 eq6320
  have eq6322 : (σ (M.op x (M.op x x))) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq6321
       have i₂ := eq6066
       grind)
    | exact superpose eq6066 eq6321
    | exact resolve eq6321 eq6066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6066 eq6321
  have eq6333 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq5738 (M.op x (M.op x X0))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq5738
    | exact resolve eq5738 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6351 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq5714 (M.op (M.op x x) X0)
       have i₂ := eq5738 X0
       grind)
    | exact superpose eq5738 eq5714
    | exact resolve eq5714 eq5738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5738
  have eq6377 : ∀ X0 : G, (M.op x (M.op x (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq5714 X0
       have i₂ := eq6333 X0
       grind)
    | exact superpose eq6333 eq5714
    | exact resolve eq5714 eq6333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5714
  have eq6385 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op (M.op x (M.op x X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6145 X0 X1
       have i₂ := eq6333 X0
       grind)
    | exact superpose eq6333 eq6145
    | exact resolve eq6145 eq6333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6145
  have eq6525 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x (M.op (M.op (M.op x x) (M.op x x)) (M.op x x))))) := by
    first
    | (have i₁ := eq1654 (M.op x x)
       have i₂ := eq6351 (M.op (M.op (M.op x x) (M.op x x)) (M.op x x))
       grind)
    | exact superpose eq6351 eq1654
    | exact resolve eq1654 eq6351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq6526 : (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ (M.op x (M.op (M.op (M.op x x) (M.op x x)) (M.op x x))))) := by
    first
    | (have i₁ := eq1649 (M.op x x)
       have i₂ := eq6351 (M.op (M.op (M.op x x) (M.op x x)) (M.op x x))
       grind)
    | exact superpose eq6351 eq1649
    | exact resolve eq1649 eq6351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6351
  have eq6544 : (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ (M.op x (M.op (M.op x (M.op (M.op x x) x)) (M.op x x))))) := by
    first
    | (have i₁ := eq6526
       have i₂ := eq1664 x x x
       grind)
    | exact superpose eq1664 eq6526
    | exact resolve eq6526 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq6545 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x (M.op (M.op x (M.op (M.op x x) x)) (M.op x x))))) := by
    first
    | (have i₁ := eq6525
       have i₂ := eq1664 x x x
       grind)
    | exact superpose eq1664 eq6525
    | exact resolve eq6525 eq1664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq6525
  have eq6570 : (τ (M.op x x)) = (M.op (τ (M.op x x)) (τ x)) := by
    first
    | (have i₁ := eq6544
       have i₂ := eq1674 x x
       grind)
    | exact superpose eq1674 eq6544
    | exact resolve eq6544 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6544
  have eq6571 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq6545
       have i₂ := eq1674 x x
       grind)
    | exact superpose eq1674 eq6545
    | exact resolve eq6545 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674 eq6545
  have eq6652 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) (M.op y (M.op (M.op x X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 y (M.op x X0)
       have i₂ := eq6123 X0
       grind)
    | exact superpose eq6123 eq9
    | exact resolve eq9 eq6123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6714 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op (M.op x (M.op x X0)) y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1426 (M.op y X0) y
       have i₂ := eq6333 X0
       grind)
    | exact superpose eq6333 eq1426
    | exact resolve eq1426 eq6333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7490 : ∀ X0 : G, (M.op (τ y) (M.op (τ x) (M.op (τ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (τ x) (τ y)
       have i₂ := eq5688 (M.op (τ x) (M.op (τ y) X0))
       grind)
    | exact superpose eq5688 eq9
    | exact resolve eq9 eq5688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7505 : ∀ X0 : G, (τ (M.op (τ x) (τ y))) = (M.op (M.op X0 (τ (M.op (τ x) (τ y)))) (M.op X0 (τ (M.op (τ y) (M.op (τ x) (τ y)))))) := by
    intro X0
    first
    | (have i₁ := eq1130 (M.op (τ x) (τ y)) X0
       have i₂ := eq5688 (M.op (τ x) (τ y))
       grind)
    | exact superpose eq5688 eq1130
    | exact resolve eq1130 eq5688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq7518 : ∀ X0 : G, (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ y) (M.op (τ x) (τ y)))) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1699 (M.op (τ x) (τ y)) X0
       have i₂ := eq5688 (M.op (τ x) (τ y))
       grind)
    | exact superpose eq5688 eq1699
    | exact resolve eq1699 eq5688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5688
  have eq7657 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq5689 (M.op (σ x) (M.op (σ y) X0))
       grind)
    | exact superpose eq5689 eq9
    | exact resolve eq9 eq5689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5689
  have eq7824 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x x)) X0)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq5696 (M.op (σ x) (M.op (σ (M.op x x)) X0))
       have i₂ := eq1698 x X0
       grind)
    | exact superpose eq1698 eq5696
    | exact resolve eq5696 eq1698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698 eq5696
  have eq7874 : ∀ X0 : G, (M.op (τ x) (M.op (τ (M.op x x)) X0)) = (M.op (τ y) (M.op (τ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq5697 (M.op (τ x) (M.op (τ (M.op x x)) X0))
       have i₂ := eq1699 x X0
       grind)
    | exact superpose eq1699 eq5697
    | exact resolve eq5697 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699 eq5697
  have eq8537 : ∀ X0 : G, (M.op (τ y) (M.op (τ x) X0)) = (M.op (τ x) (M.op (τ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq7490 (M.op (τ x) (M.op (τ y) X0))
       have i₂ := eq7490 X0
       grind)
    | exact superpose eq7490 eq7490
    | exact resolve eq7490 eq7490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8590 : ∀ X0 : G, (M.op (τ x) (M.op (τ y) (M.op (τ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7490 X0
       have i₂ := eq8537 (M.op (τ y) X0)
       grind)
    | exact superpose eq8537 eq7490
    | exact resolve eq7490 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7490
  have eq8598 : ∀ X0 : G, (τ (M.op (τ x) (τ y))) = (M.op (M.op X0 (τ (M.op (τ x) (τ y)))) (M.op X0 (τ (M.op (τ x) (M.op (τ y) (τ y)))))) := by
    intro X0
    first
    | (have i₁ := eq7505 X0
       have i₂ := eq8537 (τ y)
       grind)
    | exact superpose eq8537 eq7505
    | exact resolve eq7505 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7505
  have eq8601 : ∀ X0 : G, (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ x) (M.op (τ y) (τ y)))) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7518 X0
       have i₂ := eq8537 (τ y)
       grind)
    | exact superpose eq8537 eq7518
    | exact resolve eq7518 eq8537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7518 eq8537
  have eq8646 : ∀ X0 : G, (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ x) (τ (M.op y y)))) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8601 X0
       have i₂ := eq944 y
       grind)
    | exact superpose eq944 eq8601
    | exact resolve eq8601 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8601
  have eq8649 : ∀ X0 : G, (τ (M.op (τ x) (τ y))) = (M.op (M.op X0 (τ (M.op (τ x) (τ y)))) (M.op X0 (τ (M.op (τ x) (τ (M.op y y)))))) := by
    intro X0
    first
    | (have i₁ := eq8598 X0
       have i₂ := eq944 y
       grind)
    | exact superpose eq944 eq8598
    | exact resolve eq8598 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8598
  have eq8683 : ∀ X0 : G, (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ x) (τ x))) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8646 X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq8646
    | exact resolve eq8646 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8646
  have eq8686 : ∀ X0 : G, (τ (M.op (τ x) (τ y))) = (M.op (M.op X0 (τ (M.op (τ x) (τ y)))) (M.op X0 (τ (M.op (τ x) (τ x))))) := by
    intro X0
    first
    | (have i₁ := eq8649 X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq8649
    | exact resolve eq8649 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8649
  have eq8715 : ∀ X0 : G, (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (M.op (τ x) (τ y))) (M.op (τ (τ (M.op x x))) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8683 X0
       have i₂ := eq944 x
       grind)
    | exact superpose eq944 eq8683
    | exact resolve eq8683 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8683
  have eq8718 : ∀ X0 : G, (τ (M.op (τ x) (τ y))) = (M.op (M.op X0 (τ (M.op (τ x) (τ y)))) (M.op X0 (τ (τ (M.op x x))))) := by
    intro X0
    first
    | (have i₁ := eq8686 X0
       have i₂ := eq944 x
       grind)
    | exact superpose eq944 eq8686
    | exact resolve eq8686 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8686
  have eq8780 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq7657 (M.op (σ x) (M.op (σ y) X0))
       have i₂ := eq7657 X0
       grind)
    | exact superpose eq7657 eq7657
    | exact resolve eq7657 eq7657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8781 : (σ y) = (M.op (σ y) (M.op (σ x) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq7657 (σ y)
       have i₂ := eq950 y
       grind)
    | exact superpose eq950 eq7657
    | exact resolve eq7657 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8821 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq8781
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq8781
    | exact resolve eq8781 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8781
  have eq8830 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7657 X0
       have i₂ := eq8780 (M.op (σ y) X0)
       grind)
    | exact superpose eq8780 eq7657
    | exact resolve eq7657 eq8780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7657
  have eq8869 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq8821
       have i₂ := eq8780 (σ x)
       grind)
    | exact superpose eq8780 eq8821
    | exact resolve eq8821 eq8780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8780 eq8821
  have eq9023 : ∀ X0 X1 : G, (M.op X0 (M.op (τ x) (M.op (M.op (τ y) (M.op (τ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ x) (M.op (τ y) (M.op (τ y) X0))
       have i₂ := eq8590 X0
       grind)
    | exact superpose eq8590 eq9
    | exact resolve eq9 eq8590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9582 : ∀ X0 : G, (M.op (τ x) X0) = (M.op (τ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq1262 X0 x
       have i₂ := eq6570
       grind)
    | exact superpose eq6570 eq1262
    | exact resolve eq1262 eq6570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6570
  have eq9603 : ∀ X0 : G, (M.op (τ y) (M.op (τ y) X0)) = (M.op (τ x) (M.op (τ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq7874 X0
       have i₂ := eq9582 X0
       grind)
    | exact superpose eq9582 eq7874
    | exact resolve eq7874 eq9582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7874
  have eq9630 : ∀ X0 : G, (M.op (τ x) (M.op (τ x) (M.op (τ x) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8590 X0
       have i₂ := eq9603 X0
       grind)
    | exact superpose eq9603 eq8590
    | exact resolve eq8590 eq9603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8590
  have eq9634 : ∀ X0 X1 : G, (M.op X0 (M.op (τ x) (M.op (M.op (τ x) (M.op (τ x) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9023 X0 X1
       have i₂ := eq9603 X0
       grind)
    | exact superpose eq9603 eq9023
    | exact resolve eq9023 eq9603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9023 eq9603
  have eq9727 : (τ (τ (M.op x x))) = (M.op (τ (τ (M.op x x))) (τ (M.op (τ (M.op x x)) (M.op (M.op (τ x) (τ (M.op x x))) (τ (M.op x x)))))) := by
    first
    | (have i₁ := eq1649 (τ (M.op x x))
       have i₂ := eq9582 (τ (M.op x x))
       grind)
    | exact superpose eq9582 eq1649
    | exact resolve eq1649 eq9582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq9796 : (τ (τ (M.op x x))) = (M.op (τ (τ (M.op x x))) (τ (M.op (τ x) (M.op (M.op (τ x) (τ (M.op x x))) (τ (M.op x x)))))) := by
    first
    | (have i₁ := eq9727
       have i₂ := eq9582 (M.op (M.op (τ x) (τ (M.op x x))) (τ (M.op x x)))
       grind)
    | exact superpose eq9582 eq9727
    | exact resolve eq9727 eq9582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9582 eq9727
  have eq9865 : (τ (τ (M.op x x))) = (M.op (τ (τ (M.op x x))) (τ (M.op (τ x) (M.op (τ x) (τ (M.op x x)))))) := by
    first
    | (have i₁ := eq9796
       have i₂ := eq1775 x (τ (M.op x x))
       grind)
    | exact superpose eq1775 eq9796
    | exact resolve eq9796 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9796
  have eq9915 : (τ (τ (M.op x x))) = (M.op (τ (τ (M.op x x))) (τ (τ (M.op x (M.op x (M.op x x)))))) := by
    first
    | (have i₁ := eq9865
       have i₂ := eq2375 x
       grind)
    | exact superpose eq2375 eq9865
    | exact resolve eq9865 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375 eq9865
  have eq9950 : (τ (τ (M.op x x))) = (M.op (τ (τ (M.op x x))) (τ (τ x))) := by
    first
    | (have i₁ := eq9915
       have i₂ := eq6377 x
       grind)
    | exact superpose eq6377 eq9915
    | exact resolve eq9915 eq6377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9915
  have eq10068 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq1364 X0 x
       have i₂ := eq6571
       grind)
    | exact superpose eq6571 eq1364
    | exact resolve eq1364 eq6571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364 eq6571
  have eq10087 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq7824 X0
       have i₂ := eq10068 X0
       grind)
    | exact superpose eq10068 eq7824
    | exact resolve eq7824 eq10068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7824 eq10068
  have eq10111 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8830 X0
       have i₂ := eq10087 X0
       grind)
    | exact superpose eq10087 eq8830
    | exact resolve eq8830 eq10087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8830 eq10087
  have eq11242 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ (k X0 y)) (σ X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq1426 (σ y) (σ X0)
       have i₂ := eq5708 X0
       grind)
    | exact superpose eq5708 eq1426
    | (have j1 := eq5708 X0
       grind)
    | exact resolve eq1426 eq5708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5708
  have eq11245 : ∀ X0 : G, (σ (M.op y y)) = (M.op (M.op (σ (k X0 y)) (σ X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq11242 X0
       have i₂ := eq950 y
       grind)
    | exact superpose eq950 eq11242
    | (have j0 := eq11242 X0
       grind)
    | exact resolve eq11242 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11242
  have eq11298 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (k X0 y)) (σ X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq11245 X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq11245
    | (have j0 := eq11245 X0
       grind)
    | exact resolve eq11245 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11245
  have eq11610 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op y X1) (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5805 (M.op X1 X0) (M.op y X1)
       have i₂ := eq9 X0 y X1
       grind)
    | exact superpose eq9 eq5805
    | exact resolve eq5805 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5805
  have eq11994 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op y X1) (M.op y x)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5980 (M.op X1 X0) (M.op y X1)
       have i₂ := eq9 X0 y X1
       grind)
    | exact superpose eq9 eq5980
    | exact resolve eq5980 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5980
  have eq12286 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op y (M.op (M.op x (M.op y (M.op x (M.op y X1)))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6157 X1 (M.op y (M.op (M.op x (M.op y (M.op x (M.op y X1)))) X0))
       have i₂ := eq6157 (M.op x (M.op y X1)) X0
       grind)
    | exact superpose eq6157 eq6157
    | exact resolve eq6157 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12306 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X1)) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op x (M.op y X1)) X0) X1 y
       have i₂ := eq6157 X1 X0
       grind)
    | exact superpose eq6157 eq9
    | exact resolve eq9 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12310 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op y (M.op (M.op x (M.op y X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op y (M.op (M.op x (M.op y X2)) X0)) X1 X2
       have i₂ := eq6157 X2 X0
       grind)
    | exact superpose eq6157 eq9
    | exact resolve eq9 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12311 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op y (M.op (M.op x (M.op y X1)) X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op y (M.op (M.op x (M.op y X1)) X0))
       have i₂ := eq6157 X1 X0
       grind)
    | exact superpose eq6157 eq9
    | exact resolve eq9 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12353 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op (M.op X0 y) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6157 X0 X1
       have i₂ := eq12306 X1 X0
       grind)
    | exact superpose eq12306 eq6157
    | exact resolve eq6157 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6157
  have eq12357 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op y (M.op (M.op X2 y) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12310 X0 X1 X2
       have i₂ := eq12306 X0 X2
       grind)
    | exact superpose eq12306 eq12310
    | exact resolve eq12310 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12310
  have eq12358 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op y (M.op (M.op X1 y) X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12311 X0 X1 X2
       have i₂ := eq12306 X0 X1
       grind)
    | exact superpose eq12306 eq12311
    | exact resolve eq12311 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12311
  have eq12370 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op y (M.op (M.op x X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6652 X0 X1
       have i₂ := eq12306 (M.op y (M.op (M.op x X0) X1)) X0
       grind)
    | exact superpose eq12306 eq6652
    | exact resolve eq6652 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6652
  have eq12394 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op y (M.op (M.op (M.op x (M.op y X1)) y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12286 X0 X1
       have i₂ := eq12306 X0 (M.op x (M.op y X1))
       grind)
    | exact superpose eq12306 eq12286
    | exact resolve eq12286 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12286
  have eq12439 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op y (M.op (M.op X2 y) X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1605 X0 X1 X2
       have i₂ := eq12357 X2 X1 X2
       grind)
    | exact superpose eq12357 eq1605
    | exact resolve eq1605 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq12541 : ∀ X0 : G, (τ (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op y (M.op (M.op (τ X0) y) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1974 X0 x
       have i₂ := eq12357 (τ X0) x (τ X0)
       grind)
    | exact superpose eq12357 eq1974
    | exact resolve eq1974 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq12579 : (τ (M.op (τ x) (τ y))) = (M.op y (M.op (M.op (τ (M.op (τ x) (τ y))) y) (τ (τ (M.op x x))))) := by
    first
    | (have i₁ := eq8718 x
       have i₂ := eq12357 (τ (τ (M.op x x))) x (τ (M.op (τ x) (τ y)))
       grind)
    | exact superpose eq12357 eq8718
    | exact resolve eq8718 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8718
  have eq12637 : ∀ X0 : G, (M.op (M.op (M.op x (M.op x X0)) y) (M.op y X0)) = (M.op y (M.op (M.op X0 y) X0)) := by
    intro X0
    first
    | (have i₁ := eq6714 X0
       have i₂ := eq12357 X0 y X0
       grind)
    | exact superpose eq12357 eq6714
    | exact resolve eq6714 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714
  have eq12651 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op y (M.op (M.op X1 y) x)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11994 X0 X1
       have i₂ := eq12357 x y X1
       grind)
    | exact superpose eq12357 eq11994
    | exact resolve eq11994 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11994
  have eq12680 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op y (M.op (M.op (M.op X1 y) y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12394 X0 X1
       have i₂ := eq12306 y X1
       grind)
    | exact superpose eq12306 eq12394
    | exact resolve eq12394 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12394
  have eq13382 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op (M.op x (M.op x (M.op x (M.op x X1)))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6385 X1 (M.op x (M.op (M.op x (M.op x (M.op x (M.op x X1)))) X0))
       have i₂ := eq6385 (M.op x (M.op x X1)) X0
       grind)
    | exact superpose eq6385 eq6385
    | exact resolve eq6385 eq6385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13383 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y (M.op (M.op (M.op x (M.op x X1)) y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6385 X1 (M.op y (M.op (M.op (M.op x (M.op x X1)) y) X0))
       have i₂ := eq12353 (M.op x (M.op x X1)) X0
       grind)
    | exact superpose eq12353 eq6385
    | exact resolve eq6385 eq12353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6385
  have eq13439 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13382 X0 X1
       have i₂ := eq6377 (M.op x X1)
       grind)
    | exact superpose eq6377 eq13382
    | exact resolve eq13382 eq6377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6377 eq13382
  have eq13859 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op (M.op x (M.op y X0)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11610 X1 (M.op x X0)
       have i₂ := eq6123 X0
       grind)
    | exact superpose eq6123 eq11610
    | exact resolve eq11610 eq6123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13860 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op (M.op x (M.op x X0)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11610 X1 (M.op y X0)
       have i₂ := eq6333 X0
       grind)
    | exact superpose eq6333 eq11610
    | exact resolve eq11610 eq6333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6333
  have eq13876 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op y (M.op (M.op y y) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11610 X1 (M.op y (M.op (M.op y y) X0))
       have i₂ := eq12353 y X0
       grind)
    | exact superpose eq12353 eq11610
    | exact resolve eq11610 eq12353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13939 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) (M.op x y)) (M.op X0 (M.op (M.op (M.op (M.op y X0) (M.op x y)) (M.op (M.op y X0) (M.op x y))) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1666 (M.op (M.op y X0) (M.op x y)) X1
       have i₂ := eq11610 (M.op (M.op (M.op (M.op y X0) (M.op x y)) (M.op (M.op y X0) (M.op x y))) X1) X0
       grind)
    | exact superpose eq11610 eq1666
    | exact resolve eq1666 eq11610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13949 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op (M.op (M.op y X0) (M.op x y)) (M.op (M.op y X0) (M.op x y))) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13939 X0 X1
       have i₂ := eq11610 (M.op X0 (M.op (M.op (M.op (M.op y X0) (M.op x y)) (M.op (M.op y X0) (M.op x y))) X1)) X0
       grind)
    | exact superpose eq11610 eq13939
    | exact resolve eq13939 eq11610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13939
  have eq13970 : ∀ X0 X1 : G, (M.op (M.op y (M.op x X0)) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13876 X0 X1
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq13876
    | exact resolve eq13876 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13876
  have eq13977 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op y (M.op (M.op (M.op x X0) y) y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13860 X0 X1
       have i₂ := eq12357 y x (M.op x X0)
       grind)
    | exact superpose eq12357 eq13860
    | exact resolve eq13860 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13860
  have eq13978 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op y (M.op (M.op (M.op y X0) y) y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13859 X0 X1
       have i₂ := eq12357 y x (M.op y X0)
       grind)
    | exact superpose eq12357 eq13859
    | exact resolve eq13859 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13859
  have eq13983 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op y (M.op (M.op (M.op x y) y) (M.op x y))) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13949 X0 X1
       have i₂ := eq12357 (M.op x y) (M.op y X0) (M.op x y)
       grind)
    | exact superpose eq12357 eq13949
    | exact resolve eq13949 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13949
  have eq13997 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13970 X0 X1
       have i₂ := eq6123 X0
       grind)
    | exact superpose eq6123 eq13970
    | exact resolve eq13970 eq6123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6123 eq13970
  have eq14003 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op x (M.op y (M.op x y))) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13983 X0 X1
       have i₂ := eq12680 (M.op x y) x
       grind)
    | exact superpose eq12680 eq13983
    | exact resolve eq13983 eq12680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12680 eq13983
  have eq14011 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13997 X0 X1
       have i₂ := eq12306 X1 X0
       grind)
    | exact superpose eq12306 eq13997
    | exact resolve eq13997 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13997
  have eq14016 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op (M.op x y) y) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14003 X0 X1
       have i₂ := eq12306 X1 (M.op x y)
       grind)
    | exact superpose eq12306 eq14003
    | exact resolve eq14003 eq12306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12306 eq14003
  have eq14033 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op y X1) y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11610 X0 X1
       have i₂ := eq14011 (M.op y X1) X0
       grind)
    | exact superpose eq14011 eq11610
    | exact resolve eq11610 eq14011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11610
  have eq14052 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op y y) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14016 X0 X1
       have i₂ := eq5690 y
       grind)
    | exact superpose eq5690 eq14016
    | exact resolve eq14016 eq5690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5690 eq14016
  have eq14061 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op y (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13978 X0 X1
       have i₂ := eq14033 y X0
       grind)
    | exact superpose eq14033 eq13978
    | exact resolve eq13978 eq14033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13978 eq14033
  have eq14065 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14052 X0 X1
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq14052
    | exact resolve eq14052 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14052
  have eq14069 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x (M.op (M.op x X0) y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13977 X0 X1
       have i₂ := eq14061 (M.op (M.op x X0) y) X1
       grind)
    | exact superpose eq14061 eq13977
    | exact resolve eq13977 eq14061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13977 eq14061
  have eq14074 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14069 X0 X1
       have i₂ := eq13439 y X0
       grind)
    | exact superpose eq13439 eq14069
    | exact resolve eq14069 eq13439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14069
  have eq14078 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op X0 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14074 X0 X1
       have i₂ := eq14011 X0 X1
       grind)
    | exact superpose eq14011 eq14074
    | exact resolve eq14074 eq14011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011 eq14074
  have eq14081 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq14065 X0 (M.op y x)
       have i₂ := eq6121
       grind)
    | exact superpose eq6121 eq14065
    | exact resolve eq14065 eq6121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14097 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op x (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14065 X1 (M.op x (M.op x X0))
       have i₂ := eq14065 x X0
       grind)
    | exact superpose eq14065 eq14065
    | exact resolve eq14065 eq14065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14152 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X1 (M.op x X0)
       have i₂ := eq14065 (M.op x X0) X0
       grind)
    | exact superpose eq14065 eq1623
    | exact resolve eq1623 eq14065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq14159 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X1 y) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12353 X1 (M.op (M.op X1 y) (M.op x X0))
       have i₂ := eq14065 (M.op X1 y) X0
       grind)
    | exact superpose eq14065 eq12353
    | exact resolve eq12353 eq14065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14172 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq10111 (M.op x X0)
       have i₂ := eq14065 (σ x) X0
       grind)
    | exact superpose eq14065 eq10111
    | exact resolve eq10111 eq14065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10111
  have eq14177 : ∀ X0 : G, (M.op x X0) = (M.op (τ x) X0) := by
    intro X0
    first
    | (have i₁ := eq9630 (M.op x X0)
       have i₂ := eq14065 (τ x) X0
       grind)
    | exact superpose eq14065 eq9630
    | exact resolve eq9630 eq14065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14178 : ∀ X0 : G, (M.op (τ x) (M.op (τ x) X0)) = (M.op (τ x) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9630 (M.op (τ x) (M.op x X0))
       have i₂ := eq14065 (τ x) X0
       grind)
    | exact superpose eq14065 eq9630
    | exact resolve eq9630 eq14065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9630
  have eq14191 : ∀ X0 X1 : G, (M.op X0 (M.op (τ x) (M.op (M.op (τ x) (M.op x X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9634 X0 X1
       have i₂ := eq14178 X0
       grind)
    | exact superpose eq14178 eq9634
    | exact resolve eq9634 eq14178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9634 eq14178
  have eq14291 : ∀ X0 : G, (M.op (τ (M.op x (τ y))) (M.op (τ (M.op x (τ y))) (M.op (τ (τ (M.op x x))) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8715 X0
       have i₂ := eq14177 (τ y)
       grind)
    | exact superpose eq14177 eq8715
    | exact resolve eq8715 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8715
  have eq14306 : (τ (M.op x (τ y))) = (M.op y (M.op (M.op (τ (M.op x (τ y))) y) (τ (τ (M.op x x))))) := by
    first
    | (have i₁ := eq12579
       have i₂ := eq14177 (τ y)
       grind)
    | exact superpose eq14177 eq12579
    | exact resolve eq12579 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12579
  have eq14363 : (σ y) = (M.op x (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq8869
       have i₂ := eq14172 (M.op (σ y) (σ x))
       grind)
    | exact superpose eq14172 eq8869
    | exact resolve eq8869 eq14172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8869
  have eq14376 : (σ (M.op x (M.op x x))) = (M.op x (σ (M.op x x))) := by
    first
    | (have i₁ := eq6322
       have i₂ := eq14172 (σ (M.op x x))
       grind)
    | exact superpose eq14172 eq6322
    | exact resolve eq6322 eq14172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6322
  have eq14385 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14172 (σ y)
       grind)
    | exact superpose eq14172 eq16
    | exact resolve eq16 eq14172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14452 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op y (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12370 X0 X1
       have i₂ := eq14152 X0 X1
       grind)
    | exact superpose eq14152 eq12370
    | exact resolve eq12370 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12370
  have eq14453 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13439 X0 X1
       have i₂ := eq14152 X1 X0
       grind)
    | exact superpose eq14152 eq13439
    | exact resolve eq13439 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13439
  have eq14464 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y (M.op (M.op (M.op x X1) y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13383 X0 X1
       have i₂ := eq14152 (M.op x X1) y
       grind)
    | exact superpose eq14152 eq13383
    | exact resolve eq13383 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13383
  have eq14465 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) X0)) = (M.op (M.op (M.op x X0) y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq12637 X0
       have i₂ := eq14152 (M.op x X0) y
       grind)
    | exact superpose eq14152 eq12637
    | exact resolve eq12637 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12637
  have eq14527 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op (M.op (τ x) (M.op x X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14191 X0 X1
       have i₂ := eq14177 (M.op (M.op (τ x) (M.op x X0)) X1)
       grind)
    | exact superpose eq14177 eq14191
    | exact resolve eq14191 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14191
  have eq14534 : (τ (M.op x (τ y))) = (M.op y (M.op (M.op y (τ (M.op x (τ y)))) (τ (τ (M.op x x))))) := by
    first
    | (have i₁ := eq14306
       have i₂ := eq14078 (τ (M.op x (τ y))) (τ (τ (M.op x x)))
       grind)
    | exact superpose eq14078 eq14306
    | exact resolve eq14306 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14306
  have eq14543 : ∀ X0 : G, (M.op x (M.op x (M.op (τ (τ (M.op x x))) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14291 X0
       have i₂ := eq14097 (M.op (τ (τ (M.op x x))) X0) (τ (M.op x (τ y)))
       grind)
    | exact superpose eq14097 eq14291
    | exact resolve eq14291 eq14097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14097 eq14291
  have eq14652 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op x (σ (M.op x x)))) := by
    first
    | (have i₁ := eq6109
       have i₂ := eq14376
       grind)
    | exact superpose eq14376 eq6109
    | exact resolve eq6109 eq14376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6109 eq14376
  have eq14722 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) X0)) = (M.op (M.op y (M.op x X0)) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq14465 X0
       have i₂ := eq14078 (M.op x X0) (M.op y X0)
       grind)
    | exact superpose eq14078 eq14465
    | exact resolve eq14465 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14465
  have eq14723 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y (M.op (M.op y (M.op x X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14464 X0 X1
       have i₂ := eq14078 (M.op x X1) X0
       grind)
    | exact superpose eq14078 eq14464
    | exact resolve eq14464 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14464
  have eq14756 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op (M.op x (M.op x X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14527 X0 X1
       have i₂ := eq14177 (M.op x X0)
       grind)
    | exact superpose eq14177 eq14527
    | exact resolve eq14527 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14527
  have eq14807 : (σ (M.op x y)) = (M.op x (M.op (σ (M.op x y)) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq14652
       have i₂ := eq14453 (σ (M.op x x)) (σ (M.op x y))
       grind)
    | exact superpose eq14453 eq14652
    | exact resolve eq14652 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14652
  have eq14819 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) X0)) = (M.op y (M.op (M.op (M.op x X0) y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14722 X0
       have i₂ := eq12357 X0 y (M.op x X0)
       grind)
    | exact superpose eq12357 eq14722
    | exact resolve eq14722 eq12357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12357 eq14722
  have eq14820 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y (M.op (M.op x (M.op y X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14723 X0 X1
       have i₂ := eq14453 X1 y
       grind)
    | exact superpose eq14453 eq14723
    | exact resolve eq14723 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14723
  have eq14835 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op (M.op x X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14756 X0 X1
       have i₂ := eq14152 (M.op x X0) X1
       grind)
    | exact superpose eq14152 eq14756
    | exact resolve eq14756 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14756
  have eq14859 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) X0)) = (M.op y (M.op (M.op y (M.op x X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq14819 X0
       have i₂ := eq14078 (M.op x X0) X0
       grind)
    | exact superpose eq14078 eq14819
    | exact resolve eq14819 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14819
  have eq14860 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y (M.op (M.op y X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14820 X0 X1
       have i₂ := eq14152 (M.op y X1) X0
       grind)
    | exact superpose eq14152 eq14820
    | exact resolve eq14820 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14820
  have eq14877 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14835 X0 X1
       have i₂ := eq14152 X0 X1
       grind)
    | exact superpose eq14152 eq14835
    | exact resolve eq14835 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14835
  have eq14889 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) X0)) = (M.op y (M.op (M.op x (M.op y X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq14859 X0
       have i₂ := eq14453 X0 y
       grind)
    | exact superpose eq14453 eq14859
    | exact resolve eq14859 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14859
  have eq14901 : (τ (M.op x (τ y))) = (M.op (τ (M.op x (τ y))) (M.op x (τ (τ (M.op x x))))) := by
    first
    | (have i₁ := eq14534
       have i₂ := eq14860 (τ (τ (M.op x x))) (τ (M.op x (τ y)))
       grind)
    | exact superpose eq14860 eq14534
    | exact resolve eq14534 eq14860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14534
  have eq14924 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) X0)) = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14889 X0
       have i₂ := eq14152 (M.op y X0) X0
       grind)
    | exact superpose eq14152 eq14889
    | exact resolve eq14889 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14889
  have eq14927 : (τ (M.op x (τ y))) = (M.op x (M.op (τ (M.op x (τ y))) (τ (τ (M.op x x))))) := by
    first
    | (have i₁ := eq14901
       have i₂ := eq14453 (τ (τ (M.op x x))) (τ (M.op x (τ y)))
       grind)
    | exact superpose eq14453 eq14901
    | exact resolve eq14901 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14901
  have eq14945 : ∀ X0 : G, (M.op y (M.op (M.op X0 y) X0)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14924 X0
       have i₂ := eq14860 X0 X0
       grind)
    | exact superpose eq14860 eq14924
    | exact resolve eq14924 eq14860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14860 eq14924
  have eq14963 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X2 (M.op x X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12439 X0 X1 X2
       have i₂ := eq14945 X2
       grind)
    | exact superpose eq14945 eq12439
    | exact resolve eq12439 eq14945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12439
  have eq15057 : ∀ X0 : G, (τ (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op (τ X0) (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12541 X0
       have i₂ := eq14945 (τ X0)
       grind)
    | exact superpose eq14945 eq12541
    | exact resolve eq12541 eq14945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12541 eq14945
  have eq15141 : ∀ X0 : G, (τ (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op x (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15057 X0
       have i₂ := eq14453 (τ X0) (τ X0)
       grind)
    | exact superpose eq14453 eq15057
    | exact resolve eq15057 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15057
  have eq15237 : ∀ X0 : G, (τ (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq15141 X0
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq15141
    | exact resolve eq15141 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15141
  have eq15726 : (σ (M.op x x)) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq950 x
       have i₂ := eq14172 (σ x)
       grind)
    | exact superpose eq14172 eq950
    | exact resolve eq950 eq14172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq14172
  have eq15893 : (σ (M.op x y)) = (M.op x (M.op (σ (M.op x y)) (M.op x (σ x)))) := by
    first
    | (have i₁ := eq14807
       have i₂ := eq15726
       grind)
    | exact superpose eq15726 eq14807
    | exact resolve eq14807 eq15726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807 eq15726
  have eq15929 : (σ (M.op x y)) = (M.op x (M.op x (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | (have i₁ := eq15893
       have i₂ := eq14453 (σ x) (σ (M.op x y))
       grind)
    | exact superpose eq14453 eq15893
    | exact resolve eq15893 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15893
  have eq16020 : (τ (M.op x x)) = (M.op x (τ x)) := by
    first
    | (have i₁ := eq944 x
       have i₂ := eq14177 (τ x)
       grind)
    | exact superpose eq14177 eq944
    | exact resolve eq944 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16039 : ∀ X0 : G, (M.op (τ (τ x)) X0) = (M.op (M.op (τ (M.op x (τ x))) (τ (τ x))) X0) := by
    intro X0
    first
    | (have i₁ := eq1262 X0 (τ x)
       have i₂ := eq14177 (τ x)
       grind)
    | exact superpose eq14177 eq1262
    | exact resolve eq1262 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq16115 : (τ (M.op x (τ x))) = (M.op (τ (M.op x (τ x))) (τ (τ x))) := by
    first
    | (have i₁ := eq9950
       have i₂ := eq16020
       grind)
    | exact superpose eq16020 eq9950
    | exact resolve eq9950 eq16020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9950
  have eq16144 : ∀ X0 : G, (M.op x (M.op x (M.op (τ (M.op x (τ x))) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14543 X0
       have i₂ := eq16020
       grind)
    | exact superpose eq16020 eq14543
    | exact resolve eq14543 eq16020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14543
  have eq16202 : (τ (M.op x (τ y))) = (M.op x (M.op (τ (M.op x (τ y))) (τ (M.op x (τ x))))) := by
    first
    | (have i₁ := eq14927
       have i₂ := eq16020
       grind)
    | exact superpose eq16020 eq14927
    | exact resolve eq14927 eq16020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14927
  have eq16259 : ∀ X0 : G, (M.op (τ (τ x)) X0) = (M.op (τ (M.op x (τ x))) X0) := by
    intro X0
    first
    | (have i₁ := eq16039 X0
       have i₂ := eq16115
       grind)
    | exact superpose eq16115 eq16039
    | exact resolve eq16039 eq16115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16039 eq16115
  have eq16287 : ∀ X0 : G, (M.op x (M.op x (M.op (τ (τ x)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16144 X0
       have i₂ := eq16259 X0
       grind)
    | exact superpose eq16259 eq16144
    | exact resolve eq16144 eq16259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16144
  have eq16332 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) X0)) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14877 X1 (M.op X1 (M.op (M.op X1 X1) X0))
       have i₂ := eq1666 X1 X0
       grind)
    | exact superpose eq1666 eq14877
    | exact resolve eq14877 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq16335 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14877 X1 (M.op y (M.op (M.op X1 y) X0))
       have i₂ := eq12353 X1 X0
       grind)
    | exact superpose eq12353 eq14877
    | exact resolve eq14877 eq12353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12353
  have eq16456 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 (M.op x X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12358 X0 X1 X2
       have i₂ := eq16335 X0 X1
       grind)
    | exact superpose eq16335 eq12358
    | exact resolve eq12358 eq16335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12358
  have eq16549 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 (M.op x x)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12651 X0 X1
       have i₂ := eq16335 x X1
       grind)
    | exact superpose eq16335 eq12651
    | exact resolve eq12651 eq16335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12651
  have eq16612 : ∀ X0 : G, (M.op x (τ (M.op X0 X0))) = (τ (M.op X0 (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq15237 X0
       have i₂ := eq16332 X0 X0
       grind)
    | exact superpose eq16332 eq15237
    | exact resolve eq15237 eq16332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15237 eq16332
  have eq17218 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq1426 X0 x
       have i₂ := eq14152 X0 x
       grind)
    | exact superpose eq14152 eq1426
    | exact resolve eq1426 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17602 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq1426 x X0
       have i₂ := eq17218 X0
       grind)
    | exact superpose eq17218 eq1426
    | exact resolve eq1426 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq17917 : ∀ X0 : G, (M.op x x) = (M.op (τ (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq17602 (τ X0)
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq17602
    | exact resolve eq17602 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18151 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq14065 X0 (M.op (σ y) (σ x))
       have i₂ := eq14363
       grind)
    | exact superpose eq14363 eq14065
    | exact resolve eq14065 eq14363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18624 : (M.op x x) = (M.op (τ (M.op x (τ x))) x) := by
    first
    | (have i₁ := eq17917 (τ x)
       have i₂ := eq14177 (τ x)
       grind)
    | exact superpose eq14177 eq17917
    | exact resolve eq17917 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18648 : (M.op x x) = (M.op (τ (τ x)) x) := by
    first
    | (have i₁ := eq18624
       have i₂ := eq16259 x
       grind)
    | exact superpose eq16259 eq18624
    | exact resolve eq18624 eq16259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16259 eq18624
  have eq18685 : (M.op (τ (τ x)) (τ (τ x))) = (M.op (M.op x x) (τ (τ x))) := by
    first
    | (have i₁ := eq17218 (τ (τ x))
       have i₂ := eq18648
       grind)
    | exact superpose eq18648 eq17218
    | exact resolve eq17218 eq18648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17218 eq18648
  have eq18694 : (M.op (τ (τ x)) (τ (τ x))) = (M.op x (τ (τ x))) := by
    first
    | (have i₁ := eq18685
       have i₂ := eq14152 x (τ (τ x))
       grind)
    | exact superpose eq14152 eq18685
    | exact resolve eq18685 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18685
  have eq18698 : (τ (M.op (τ x) (τ x))) = (M.op x (τ (τ x))) := by
    first
    | (have i₁ := eq18694
       have i₂ := eq944 (τ x)
       grind)
    | exact superpose eq944 eq18694
    | exact resolve eq18694 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18694
  have eq18699 : (τ (τ (M.op x x))) = (M.op x (τ (τ x))) := by
    first
    | (have i₁ := eq18698
       have i₂ := eq944 x
       grind)
    | exact superpose eq944 eq18698
    | exact resolve eq18698 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18698
  have eq18700 : (τ (M.op x (τ x))) = (M.op x (τ (τ x))) := by
    first
    | (have i₁ := eq18699
       have i₂ := eq16020
       grind)
    | exact superpose eq16020 eq18699
    | exact resolve eq18699 eq16020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18699
  have eq18709 : (τ (M.op x (τ y))) = (M.op x (M.op (τ (M.op x (τ y))) (M.op x (τ (τ x))))) := by
    first
    | (have i₁ := eq16202
       have i₂ := eq18700
       grind)
    | exact superpose eq18700 eq16202
    | exact resolve eq16202 eq18700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16202
  have eq18726 : (τ (M.op x (τ y))) = (M.op x (M.op x (M.op (τ (M.op x (τ y))) (τ (τ x))))) := by
    first
    | (have i₁ := eq18709
       have i₂ := eq14453 (τ (τ x)) (τ (M.op x (τ y)))
       grind)
    | exact superpose eq14453 eq18709
    | exact resolve eq18709 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18709
  have eq19037 : ∀ X0 : G, (M.op x X0) = (M.op (τ (τ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq14065 x (M.op (τ (τ x)) X0)
       have i₂ := eq16287 X0
       grind)
    | exact superpose eq16287 eq14065
    | exact resolve eq14065 eq16287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16287
  have eq20121 : ∀ X0 X1 : G, (M.op x (M.op X1 X0)) = (M.op (M.op X1 y) (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14452 X1 (M.op x (M.op X1 X0))
       have i₂ := eq14877 X1 X0
       grind)
    | exact superpose eq14877 eq14452
    | exact resolve eq14452 eq14877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20178 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op (M.op X1 y) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14877 (M.op X1 y) (M.op y (M.op X1 X0))
       have i₂ := eq14452 X1 X0
       grind)
    | exact superpose eq14452 eq14877
    | exact resolve eq14877 eq14452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20183 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op y (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20178 X0 X1
       have i₂ := eq14159 X0 X1
       grind)
    | exact superpose eq14159 eq20178
    | exact resolve eq20178 eq14159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14159 eq20178
  have eq20236 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14452 X0 X1
       have i₂ := eq20121 (M.op X0 X1) X0
       grind)
    | exact superpose eq20121 eq14452
    | exact resolve eq14452 eq20121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14452 eq20121
  have eq20486 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14065 X1 (M.op X2 (M.op X2 X0))
       have i₂ := eq20236 X2 X0
       grind)
    | exact superpose eq20236 eq14065
    | exact resolve eq14065 eq20236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20582 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op x (M.op X1 (M.op X2 (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14453 (M.op X2 (M.op X2 X0)) X1
       have i₂ := eq20236 X2 X0
       grind)
    | exact superpose eq20236 eq14453
    | exact resolve eq14453 eq20236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20583 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x (M.op X0 (M.op (σ y) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq14453 (M.op (σ y) (σ x)) X0
       have i₂ := eq14363
       grind)
    | exact superpose eq14363 eq14453
    | exact resolve eq14453 eq14363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20731 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op x X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14152 (M.op X0 X1) X2
       have i₂ := eq14453 X1 X0
       grind)
    | (have i₁ := eq14152 (M.op x X0) X1
       have i₂ := eq14453 X0 x
       grind)
    | exact superpose eq14453 eq14152
    | exact resolve eq14152 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20734 : ∀ X0 : G, x = (M.op X0 (M.op x X0)) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1667 X0 x
       have i₂ := eq14453 X0 X0
       grind)
    | (have i₁ := eq1667 x x
       have i₂ := eq14453 x x
       grind)
    | exact superpose eq14453 eq1667
    | (have j0 := eq1667 X0 x
       grind)
    | exact resolve eq1667 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq20756 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op (M.op X2 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14963 X0 X1 X2
       have i₂ := eq20731 X2 X2 X0
       grind)
    | exact superpose eq20731 eq14963
    | exact resolve eq14963 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14963
  have eq20762 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16549 X0 X1
       have i₂ := eq20731 X1 x X0
       grind)
    | exact superpose eq20731 eq16549
    | exact resolve eq16549 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16549
  have eq20763 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16456 X0 X1 X2
       have i₂ := eq20731 X1 X0 X2
       grind)
    | exact superpose eq20731 eq16456
    | exact resolve eq16456 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16456
  have eq20980 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20762 X1 (M.op X0 X0)
       have i₂ := eq17602 X0
       grind)
    | exact superpose eq17602 eq20762
    | exact resolve eq20762 eq17602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17602
  have eq21001 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (M.op x x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20762 X1 (τ (M.op X0 X0))
       have i₂ := eq17917 X0
       grind)
    | exact superpose eq17917 eq20762
    | exact resolve eq20762 eq17917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17917
  have eq21110 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21001 X0 X1
       have i₂ := eq20762 X1 x
       grind)
    | exact superpose eq20762 eq21001
    | exact resolve eq21001 eq20762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21001
  have eq21129 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20980 X0 X1
       have i₂ := eq20762 X1 x
       grind)
    | exact superpose eq20762 eq20980
    | exact resolve eq20980 eq20762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20980
  have eq21403 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 X2) (M.op x X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20756 X0 X1 X2
       have i₂ := eq21129 X2 X0
       grind)
    | exact superpose eq21129 eq20756
    | exact resolve eq20756 eq21129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20756
  have eq21552 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op x (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21403 X0 X1 X2
       have i₂ := eq14453 X0 (M.op X1 X2)
       grind)
    | exact superpose eq14453 eq21403
    | exact resolve eq21403 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21403
  have eq21822 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (M.op (τ (M.op X0 X0)) (τ (M.op x (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1775 (M.op X0 X0) X1
       have i₂ := eq21129 X0 (M.op X0 X0)
       grind)
    | exact superpose eq21129 eq1775
    | exact resolve eq1775 eq21129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775
  have eq21865 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (M.op x (τ (M.op x (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21822 X0 X1
       have i₂ := eq21110 X0 (τ (M.op x (M.op X0 X0)))
       grind)
    | exact superpose eq21110 eq21822
    | exact resolve eq21822 eq21110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21822
  have eq21900 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (M.op (τ (M.op x (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21865 X0 X1
       have i₂ := eq14152 (τ (M.op x (M.op X0 X0))) X1
       grind)
    | exact superpose eq14152 eq21865
    | exact resolve eq21865 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21865
  have eq21906 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op x (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21900 X0 X1
       have i₂ := eq21110 X0 X1
       grind)
    | exact superpose eq21110 eq21900
    | exact resolve eq21900 eq21110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21110 eq21900
  have eq22917 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x (M.op (M.op X0 (M.op x X1)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20763 (M.op X0 X1) x X2
       have i₂ := eq14453 X1 X0
       grind)
    | (have i₁ := eq20763 (M.op x X0) X1 X2
       have i₂ := eq14453 X0 X1
       grind)
    | exact superpose eq14453 eq20763
    | exact resolve eq20763 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22956 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op y x))) = (M.op (M.op X1 X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq20763 X0 X1 (M.op (M.op X1 X0) y)
       have i₂ := eq14081 (M.op X1 X0)
       grind)
    | exact superpose eq14081 eq20763
    | exact resolve eq20763 eq14081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22959 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op x (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20763 X1 X2 (M.op x (M.op (M.op X2 X1) X0))
       have i₂ := eq14877 (M.op X2 X1) X0
       grind)
    | exact superpose eq14877 eq20763
    | exact resolve eq20763 eq14877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22962 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20763 X1 X2 (M.op (M.op (M.op X2 X1) X2) X0)
       have i₂ := eq20763 X2 (M.op X2 X1) X0
       grind)
    | exact superpose eq20763 eq20763
    | exact resolve eq20763 eq20763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23010 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 X0)) = (M.op X2 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20236 X1 (M.op X2 (M.op (M.op X2 X1) X0))
       have i₂ := eq20763 X1 X2 X0
       grind)
    | exact superpose eq20763 eq20236
    | exact resolve eq20236 eq20763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20763
  have eq23135 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22959 X0 X1 X2
       have i₂ := eq21552 X0 X2 X1
       grind)
    | exact superpose eq21552 eq22959
    | exact resolve eq22959 eq21552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22959
  have eq23174 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op X0 X1) (M.op (M.op X0 (M.op x X1)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22917 X0 X1 X2
       have i₂ := eq14453 (M.op (M.op X0 (M.op x X1)) X2) (M.op X0 X1)
       grind)
    | exact superpose eq14453 eq22917
    | exact resolve eq22917 eq14453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14453 eq22917
  have eq23282 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X0 (M.op x X1)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23174 X0 X1 X2
       have i₂ := eq21552 (M.op (M.op X0 (M.op x X1)) X2) X0 X1
       grind)
    | exact superpose eq21552 eq23174
    | exact resolve eq23174 eq21552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23174
  have eq23340 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23282 X0 X1 X2
       have i₂ := eq20731 X0 X1 X2
       grind)
    | exact superpose eq20731 eq23282
    | exact resolve eq23282 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20731 eq23282
  have eq24278 : ∀ X0 : G, (M.op X0 x) = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq20183 y X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq20183
    | exact resolve eq20183 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24667 : ∀ X0 : G, (M.op (M.op y X0) x) = (M.op y (M.op (M.op X0 y) y)) := by
    intro X0
    first
    | (have i₁ := eq24278 (M.op y X0)
       have i₂ := eq14078 X0 y
       grind)
    | (have i₁ := eq24278 (M.op X0 y)
       have i₂ := eq14078 X0 y
       grind)
    | exact superpose eq14078 eq24278
    | exact resolve eq24278 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24673 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op y (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq24278 (M.op X0 y)
       have i₂ := eq14078 X0 y
       grind)
    | (have i₁ := eq24278 (M.op y X0)
       have i₂ := eq14078 X0 y
       grind)
    | exact superpose eq14078 eq24278
    | exact resolve eq24278 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24689 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op y (M.op X1 (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq20183 (M.op X0 y) X1
       have i₂ := eq24278 X0
       grind)
    | exact superpose eq24278 eq20183
    | exact resolve eq20183 eq24278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24699 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq20236 y (M.op X0 y)
       have i₂ := eq24278 X0
       grind)
    | exact superpose eq24278 eq20236
    | exact resolve eq20236 eq24278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24711 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq24673 X0
       have i₂ := eq23010 y X0 y
       grind)
    | exact superpose eq23010 eq24673
    | exact resolve eq24673 eq23010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24673
  have eq24716 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq24667 X0
       have i₂ := eq16335 y X0
       grind)
    | exact superpose eq16335 eq24667
    | exact resolve eq24667 eq16335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16335 eq24667
  have eq25343 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22962 X2 (M.op x (M.op X1 X0)) X1
       have i₂ := eq14877 X1 X0
       grind)
    | exact superpose eq14877 eq22962
    | exact resolve eq22962 eq14877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25375 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op x X0) (τ (τ x))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22962 X1 X0 (τ (τ x))
       have i₂ := eq19037 X0
       grind)
    | exact superpose eq19037 eq22962
    | exact resolve eq22962 eq19037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19037
  have eq25402 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22962 X2 X1 (M.op X1 X0)
       have i₂ := eq22962 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq22962 eq22962
    | exact resolve eq22962 eq22962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22962
  have eq25548 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (τ (τ x))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25375 X0 X1
       have i₂ := eq14152 X0 (τ (τ x))
       grind)
    | exact superpose eq14152 eq25375
    | exact resolve eq25375 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25375
  have eq25571 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25343 X0 X1 X2
       have i₂ := eq14152 (M.op X1 X0) X2
       grind)
    | exact superpose eq14152 eq25343
    | exact resolve eq25343 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25343
  have eq26156 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X2 (M.op X1 (M.op x X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23135 (M.op X1 (M.op x X0)) X1 X2
       have i₂ := eq14065 X1 X0
       grind)
    | exact superpose eq14065 eq23135
    | exact resolve eq23135 eq14065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14065
  have eq26163 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op X0 X1))) = (M.op X0 (M.op X2 (M.op y X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23135 (M.op y X1) X0 X2
       have i₂ := eq20183 X1 X0
       grind)
    | (have i₁ := eq23135 (M.op X1 X0) y X2
       have i₂ := eq20183 X0 X1
       grind)
    | exact superpose eq20183 eq23135
    | exact resolve eq23135 eq20183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26329 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op x (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14877 X1 (M.op X0 X2)
       have i₂ := eq23135 X2 X1 X0
       grind)
    | (have i₁ := eq14877 X1 (M.op X0 X2)
       have i₂ := eq23135 X2 X0 X1
       grind)
    | exact superpose eq23135 eq14877
    | exact resolve eq14877 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26759 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 X0)) = (M.op X2 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20236 X1 (M.op X2 (M.op (M.op X1 X2) X0))
       have i₂ := eq23340 X1 X2 X0
       grind)
    | exact superpose eq23340 eq20236
    | exact resolve eq20236 eq23340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23340
  have eq27519 : ∀ X0 X1 : G, (M.op y (M.op X0 x)) = (M.op X1 (M.op X1 (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq20486 (M.op X0 y) X1 y
       have i₂ := eq24278 X0
       grind)
    | exact superpose eq24278 eq20486
    | exact resolve eq20486 eq24278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28150 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op (M.op X0 X2) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25571 (M.op X0 X2) X1 X3
       have i₂ := eq23135 X2 X1 X0
       grind)
    | (have i₁ := eq25571 (M.op X0 X2) X1 X3
       have i₂ := eq23135 X2 X0 X1
       grind)
    | exact superpose eq23135 eq25571
    | exact resolve eq25571 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28161 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X1 (M.op X0 x)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25571 X1 (M.op X0 x) X2
       have i₂ := eq20762 X1 X0
       grind)
    | exact superpose eq20762 eq25571
    | exact resolve eq25571 eq20762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20762
  have eq28330 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X2 (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23135 X3 (M.op X1 X0) X2
       have i₂ := eq25571 X1 X0 (M.op X2 X3)
       grind)
    | (have i₁ := eq23135 X3 (M.op X1 X0) X2
       have i₂ := eq25571 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq25571 eq23135
    | exact resolve eq23135 eq25571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29543 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op x (M.op y (M.op x (M.op X0 y)))) := by
    intro X0
    first
    | (have i₁ := eq24699 (M.op X0 y)
       have i₂ := eq24711 X0
       grind)
    | exact superpose eq24711 eq24699
    | exact resolve eq24699 eq24711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29562 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op x (M.op x (M.op y (M.op X0 y)))) := by
    intro X0
    first
    | (have i₁ := eq29543 X0
       have i₂ := eq26163 x (M.op X0 y) x
       grind)
    | exact superpose eq26163 eq29543
    | exact resolve eq29543 eq26163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26163 eq29543
  have eq29581 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op x (M.op x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq29562 X0
       have i₂ := eq24278 X0
       grind)
    | exact superpose eq24278 eq29562
    | exact resolve eq29562 eq24278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24278 eq29562
  have eq29611 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 (M.op y X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq24716 (M.op X0 X1)
       have i₂ := eq23135 X1 y X0
       grind)
    | (have i₁ := eq24716 (M.op X0 X1)
       have i₂ := eq23135 X1 X0 y
       grind)
    | exact superpose eq23135 eq24716
    | exact resolve eq24716 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29680 : ∀ X0 X1 : G, (M.op x (M.op (M.op X1 X0) y)) = (M.op (M.op X0 (M.op y X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq29611 X0 X1
       have i₂ := eq28330 X0 X1 x y
       grind)
    | exact superpose eq28330 eq29611
    | exact resolve eq29611 eq28330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28330 eq29611
  have eq29716 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X0 (M.op y X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq29680 X0 X1
       have i₂ := eq21552 y X1 X0
       grind)
    | exact superpose eq21552 eq29680
    | exact resolve eq29680 eq21552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29680
  have eq32365 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op x (M.op X0 (M.op X0 (τ (τ x)))))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21906 (M.op X0 (τ (τ x))) X1
       have i₂ := eq25548 X0 (M.op X0 (τ (τ x)))
       grind)
    | exact superpose eq25548 eq21906
    | exact resolve eq21906 eq25548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21906 eq25548
  have eq32591 : ∀ X1 : G, (M.op x X1) = (M.op (τ (τ (τ x))) X1) := by
    intro X1
    first
    | (have i₁ := eq32365 x X1
       have i₂ := eq20236 x (τ (τ x))
       grind)
    | exact superpose eq20236 eq32365
    | exact resolve eq32365 eq20236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32365
  have eq32672 : (τ (M.op (τ (τ x)) (τ (τ x)))) = (M.op x (τ (τ (τ x)))) := by
    first
    | (have i₁ := eq944 (τ (τ x))
       have i₂ := eq32591 (τ (τ (τ x)))
       grind)
    | exact superpose eq32591 eq944
    | exact resolve eq944 eq32591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32591
  have eq32802 : (M.op x (τ (τ (τ x)))) = (τ (τ (M.op (τ x) (τ x)))) := by
    first
    | (have i₁ := eq32672
       have i₂ := eq944 (τ x)
       grind)
    | exact superpose eq944 eq32672
    | exact resolve eq32672 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32672
  have eq32826 : (M.op x (τ (τ (τ x)))) = (τ (τ (τ (M.op x x)))) := by
    first
    | (have i₁ := eq32802
       have i₂ := eq944 x
       grind)
    | exact superpose eq944 eq32802
    | exact resolve eq32802 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32802
  have eq32833 : (M.op x (τ (τ (τ x)))) = (τ (τ (M.op x (τ x)))) := by
    first
    | (have i₁ := eq32826
       have i₂ := eq16020
       grind)
    | exact superpose eq16020 eq32826
    | exact resolve eq32826 eq16020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16020 eq32826
  have eq32838 : (τ (M.op x (τ (τ x)))) = (M.op x (τ (τ (τ x)))) := by
    first
    | (have i₁ := eq32833
       have i₂ := eq18700
       grind)
    | exact superpose eq18700 eq32833
    | exact resolve eq32833 eq18700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18700 eq32833
  have eq37922 : ∀ X0 : G, (M.op x (τ (M.op X0 X0))) = (τ (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16612 X0
       have i₂ := eq23135 X0 X0 x
       grind)
    | (have i₁ := eq16612 X0
       have i₂ := eq23135 X0 x X0
       grind)
    | exact superpose eq23135 eq16612
    | exact resolve eq16612 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16612
  have eq39897 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op (M.op X0 (M.op X1 X2)) X3)) = (M.op x (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21552 X3 x (M.op (M.op X0 X1) X2)
       have i₂ := eq21552 X2 X0 X1
       grind)
    | exact superpose eq21552 eq21552
    | exact resolve eq21552 eq21552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40040 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op x (M.op (M.op X0 (M.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39897 X0 X1 X2 X3
       have i₂ := eq21552 X3 (M.op X0 X1) X2
       grind)
    | exact superpose eq21552 eq39897
    | exact resolve eq39897 eq21552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39897
  have eq40108 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40040 X0 X1 X2 X3
       have i₂ := eq21552 X3 X0 (M.op X1 X2)
       grind)
    | exact superpose eq21552 eq40040
    | exact resolve eq40040 eq21552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40040
  have eq40333 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op X0 x))) = (M.op x (M.op X1 (M.op x (M.op X0 y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq20582 (M.op y (M.op X0 x)) X1 x
       have i₂ := eq24699 X0
       grind)
    | exact superpose eq24699 eq20582
    | exact resolve eq20582 eq24699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24699
  have eq40334 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X3 (M.op X3 X1)))) = (M.op x (M.op X2 (M.op x (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20582 (M.op X0 (M.op X3 (M.op X3 X1))) X2 x
       have i₂ := eq20582 X1 X0 X3
       grind)
    | exact superpose eq20582 eq20582
    | exact resolve eq20582 eq20582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40461 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X1 (M.op X3 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21552 (M.op X3 (M.op X3 X2)) X0 X1
       have i₂ := eq20582 X2 (M.op X0 X1) X3
       grind)
    | exact superpose eq20582 eq21552
    | exact resolve eq21552 eq20582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20582
  have eq40608 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op x (M.op X2 (M.op x (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40334 X0 X1 X2 x
       have i₂ := eq40461 X2 X0 X1 x
       grind)
    | exact superpose eq40461 eq40334
    | exact resolve eq40334 eq40461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40334
  have eq40723 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op X1 (M.op y (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq40333 X0 X1
       have i₂ := eq40608 X0 y X1
       grind)
    | exact superpose eq40608 eq40333
    | exact resolve eq40333 eq40608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40333 eq40608
  have eq42398 : ∀ X0 X1 : G, (M.op X0 (M.op x (σ y))) = (M.op X1 (M.op X0 (M.op X1 (M.op (σ y) (σ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq26156 (M.op x (σ y)) X1 X0
       have i₂ := eq18151 x
       grind)
    | exact superpose eq18151 eq26156
    | exact resolve eq26156 eq18151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42405 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op x (M.op x X1)))) = (M.op X3 (M.op X2 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26156 (M.op X0 (M.op x (M.op x X1))) X3 X2
       have i₂ := eq26156 X1 x X0
       grind)
    | exact superpose eq26156 eq26156
    | exact resolve eq26156 eq26156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26156
  have eq42870 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X1) = (M.op X3 (M.op X2 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42405 X0 X1 X2 X3
       have i₂ := eq40461 X2 X0 X1 x
       grind)
    | exact superpose eq40461 eq42405
    | exact resolve eq42405 eq40461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40461 eq42405
  have eq42982 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op X0 (M.op x (σ y))) := by
    intro X0
    first
    | (have i₁ := eq42398 X0 x
       have i₂ := eq42870 (σ y) (σ x) X0 x
       grind)
    | exact superpose eq42870 eq42398
    | exact resolve eq42398 eq42870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42398 eq42870
  have eq43947 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26329 (M.op X0 X1) X2 X3
       have i₂ := eq21552 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq21552 eq26329
    | exact resolve eq26329 eq21552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26329
  have eq47651 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X1 (M.op X0 (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq22956 X1 y
       have i₂ := eq20486 x y X0
       grind)
    | (have i₁ := eq22956 X1 y
       have i₂ := eq20486 x X0 y
       grind)
    | exact superpose eq20486 eq22956
    | exact resolve eq22956 eq20486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47856 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) y) = (M.op (M.op y X1) (M.op X0 (M.op y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14078 X1 (M.op X0 (M.op y x))
       have i₂ := eq22956 (M.op X1 y) X0
       grind)
    | exact superpose eq22956 eq14078
    | exact resolve eq14078 eq22956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47904 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op X0 (M.op y x)))) = (M.op X1 (M.op (M.op X0 y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20183 (M.op X0 (M.op y x)) X1
       have i₂ := eq22956 y X0
       grind)
    | exact superpose eq22956 eq20183
    | exact resolve eq20183 eq22956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20183
  have eq47907 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op X1 (M.op (M.op X0 y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq47904 X0 X1
       have i₂ := eq43947 X1 X0 y x
       grind)
    | exact superpose eq43947 eq47904
    | exact resolve eq47904 eq43947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47904
  have eq47951 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) y) = (M.op y (M.op (M.op X1 X0) (M.op y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq47856 X0 X1
       have i₂ := eq40108 y X1 X0 (M.op y x)
       grind)
    | exact superpose eq40108 eq47856
    | exact resolve eq47856 eq40108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47856
  have eq48200 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) y) = (M.op (M.op (M.op X1 X0) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq47951 X0 X1
       have i₂ := eq22956 y (M.op X1 X0)
       grind)
    | exact superpose eq22956 eq47951
    | exact resolve eq47951 eq22956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22956 eq47951
  have eq48374 : ∀ X0 X1 : G, (M.op (M.op y (M.op X1 X0)) y) = (M.op (M.op X0 (M.op X1 y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq48200 X0 X1
       have i₂ := eq14078 (M.op X1 X0) y
       grind)
    | exact superpose eq14078 eq48200
    | exact resolve eq48200 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48200
  have eq50684 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X2 (M.op X1 (M.op X0 x))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25571 X2 (M.op X1 (M.op X0 x)) X3
       have i₂ := eq28161 X0 X1 X2
       grind)
    | exact superpose eq28161 eq25571
    | exact resolve eq25571 eq28161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50785 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X2 (M.op X1 (M.op X0 x))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50684 X0 X1 X2 X3
       have i₂ := eq28150 X0 X2 X1 X3
       grind)
    | exact superpose eq28150 eq50684
    | exact resolve eq50684 eq28150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50684
  have eq51519 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) y) = (M.op x (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq29581 (M.op X0 X1)
       have i₂ := eq21552 x X0 X1
       grind)
    | exact superpose eq21552 eq29581
    | exact resolve eq29581 eq21552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21552
  have eq51551 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op X1 (M.op X1 (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq20486 (M.op X0 x) x X1
       have i₂ := eq29581 X0
       grind)
    | exact superpose eq29581 eq20486
    | exact resolve eq20486 eq29581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20486 eq29581
  have eq51607 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X1)) y) = (M.op x (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq51519 X0 X1
       have i₂ := eq14078 (M.op X0 X1) y
       grind)
    | exact superpose eq14078 eq51519
    | exact resolve eq51519 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51519
  have eq51680 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op X0 x))) = (M.op (M.op X0 (M.op X1 y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq48374 X0 X1
       have i₂ := eq51607 X1 X0
       grind)
    | exact superpose eq51607 eq48374
    | exact resolve eq48374 eq51607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48374
  have eq51785 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) (M.op X2 y)) = (M.op (M.op X2 (M.op X0 (M.op X1 x))) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29716 X2 (M.op X0 (M.op X1 y))
       have i₂ := eq24689 X1 X0
       grind)
    | exact superpose eq24689 eq29716
    | exact resolve eq29716 eq24689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24689
  have eq51804 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 y)) (M.op X1 y)) = (M.op (M.op X1 (M.op y (M.op X0 x))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq29716 X1 (M.op y (M.op X0 y))
       have i₂ := eq27519 X0 y
       grind)
    | exact superpose eq27519 eq29716
    | exact resolve eq29716 eq27519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27519
  have eq52033 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 y)) (M.op X1 y)) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq51804 X0 X1
       have i₂ := eq50785 X0 y X1 x
       grind)
    | exact superpose eq50785 eq51804
    | exact resolve eq51804 eq50785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51804
  have eq52050 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) (M.op X2 y)) = (M.op (M.op X1 (M.op X2 X0)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51785 X0 X1 X2
       have i₂ := eq50785 X1 X0 X2 x
       grind)
    | exact superpose eq50785 eq51785
    | exact resolve eq51785 eq50785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50785 eq51785
  have eq52114 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq52033 X0 X1
       have i₂ := eq25402 y X0 (M.op X1 y)
       grind)
    | exact superpose eq25402 eq52033
    | exact resolve eq52033 eq25402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25402 eq52033
  have eq52121 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) x) = (M.op X0 (M.op (M.op (M.op X1 y) X2) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52050 X0 X1 X2
       have i₂ := eq40108 X0 (M.op X1 y) X2 y
       grind)
    | exact superpose eq40108 eq52050
    | exact resolve eq52050 eq40108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52050
  have eq52161 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) x) = (M.op X0 (M.op (M.op X1 (M.op X2 y)) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52121 X0 X1 X2
       have i₂ := eq28150 X1 X2 y y
       grind)
    | exact superpose eq28150 eq52121
    | exact resolve eq52121 eq28150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52121
  have eq52191 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) x) = (M.op X0 (M.op x (M.op X2 (M.op X1 x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52161 X0 X1 X2
       have i₂ := eq51680 X1 X2
       grind)
    | exact superpose eq51680 eq52161
    | exact resolve eq52161 eq51680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51680 eq52161
  have eq52416 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) y) = (M.op (M.op X1 X0) (M.op y (M.op X2 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25571 X0 X1 (M.op y (M.op X2 x))
       have i₂ := eq40723 X2 (M.op X0 X1)
       grind)
    | exact superpose eq40723 eq25571
    | exact resolve eq25571 eq40723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52495 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) y) = (M.op X1 (M.op (M.op X0 y) (M.op X2 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52416 X0 X1 X2
       have i₂ := eq40108 X1 X0 y (M.op X2 x)
       grind)
    | exact superpose eq40108 eq52416
    | exact resolve eq52416 eq40108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52416
  have eq52712 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) y) = (M.op X1 (M.op X0 (M.op (M.op y X2) x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52495 X0 X1 X2
       have i₂ := eq40108 X0 y X2 x
       grind)
    | exact superpose eq40108 eq52495
    | exact resolve eq52495 eq40108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52495
  have eq52867 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) y) = (M.op X1 (M.op X0 (M.op X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52712 X0 X1 X2
       have i₂ := eq24716 X2
       grind)
    | exact superpose eq24716 eq52712
    | exact resolve eq52712 eq24716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24716 eq52712
  have eq52974 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) y) = (M.op X1 (M.op X0 (M.op X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52867 X0 X1 X2
       have i₂ := eq28150 X0 X2 X1 y
       grind)
    | exact superpose eq28150 eq52867
    | exact resolve eq52867 eq28150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28150 eq52867
  have eq63410 : (M.op x (τ (τ x))) = (σ (M.op x (τ (τ (τ x))))) := by
    first
    | (have i₁ := eq11 (M.op x (τ (τ x)))
       have i₂ := eq32838
       grind)
    | exact superpose eq32838 eq11
    | exact resolve eq11 eq32838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32838
  have eq68077 : ∀ X0 : G, (M.op (M.op y X0) y) = (k (M.op y X0) y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq20236 y X0
       have i₂ := eq6129 (M.op y X0)
       grind)
    | exact superpose eq6129 eq20236
    | (have j1 := eq6129 (M.op y X0)
       grind)
    | exact resolve eq20236 eq6129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129 eq20236
  have eq69320 : (σ (M.op x y)) = (k x (σ y)) ∨ x = (τ x) := by
    first
    | (have i₁ := eq6202 x
       have i₂ := eq14177 y
       grind)
    | exact superpose eq14177 eq6202
    | (have j0 := eq6202 x
       grind)
    | exact resolve eq6202 eq14177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6202 eq14177
  have eq69484 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (τ x) ∨ x = (τ x) := by
    first
    | (have i₁ := eq5704 x
       have i₂ := eq69320
       grind)
    | exact superpose eq69320 eq5704
    | (have j0 := eq5704 x
       grind)
    | exact resolve eq5704 eq69320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5704 eq69320
  have eq69498 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (τ x) := by grind
  clear eq69484
  have eq69513 : x = (τ x) := by
    first
    | (have r₁ := eq69498
       have r₂ := eq14385
       grind)
    | exact resolve eq69498 eq14385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69498
  have eq69848 : (τ (M.op x (τ y))) = (M.op x (M.op x (M.op (τ (M.op x (τ y))) (τ x)))) := by
    first
    | (have i₁ := eq18726
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq18726
    | exact resolve eq18726 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18726
  have eq70304 : (M.op x (τ x)) = (σ (M.op x (τ (τ x)))) := by
    first
    | (have i₁ := eq63410
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq63410
    | exact resolve eq63410 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63410
  have eq70617 : (M.op x x) = (σ (M.op x (τ x))) := by
    first
    | (have i₁ := eq70304
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq70304
    | exact resolve eq70304 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70304
  have eq70946 : (τ (M.op x (τ y))) = (M.op x (M.op x (M.op (τ (M.op x (τ y))) x))) := by
    first
    | (have i₁ := eq69848
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq69848
    | exact resolve eq69848 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69848
  have eq71197 : (M.op x x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq70617
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq70617
    | exact resolve eq70617 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70617
  have eq71551 : (τ (M.op x (τ y))) = (M.op (M.op (τ (M.op x (τ y))) y) y) := by
    first
    | (have i₁ := eq70946
       have i₂ := eq51551 (τ (M.op x (τ y))) x
       grind)
    | exact superpose eq51551 eq70946
    | exact resolve eq70946 eq51551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70946
  have eq72033 : (τ (M.op x (τ y))) = (M.op (M.op y (τ (M.op x (τ y)))) y) := by
    first
    | (have i₁ := eq71551
       have i₂ := eq14078 (τ (M.op x (τ y))) y
       grind)
    | exact superpose eq14078 eq71551
    | exact resolve eq71551 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71551
  have eq72850 : x = (σ x) := by
    first
    | (have i₁ := eq11 x
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq11
    | exact resolve eq11 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72851 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq18 x X0
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq18
    | exact resolve eq18 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq73071 : ∀ X0 : G, x = (M.op (M.op (σ (k X0 y)) (σ X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq11298 X0
       have i₂ := eq72850
       grind)
    | exact superpose eq72850 eq11298
    | (have j0 := eq11298 (M.op (M.op (σ (k X0 y)) (σ X0)) (σ y))
       grind)
    | exact resolve eq11298 eq72850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11298
  have eq73104 : (σ y) = (M.op x (M.op (σ y) x)) := by
    first
    | (have i₁ := eq14363
       have i₂ := eq72850
       grind)
    | exact superpose eq72850 eq14363
    | exact resolve eq14363 eq72850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14363
  have eq73125 : (σ (M.op x y)) = (M.op x (M.op x (M.op (σ (M.op x y)) x))) := by
    first
    | (have i₁ := eq15929
       have i₂ := eq72850
       grind)
    | exact superpose eq72850 eq15929
    | exact resolve eq15929 eq72850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15929
  have eq73137 : ∀ X0 : G, (M.op (σ y) x) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq18151 X0
       have i₂ := eq72850
       grind)
    | exact superpose eq72850 eq18151
    | exact resolve eq18151 eq72850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18151
  have eq73161 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x (M.op X0 (M.op (σ y) x))) := by
    intro X0
    first
    | (have i₁ := eq20583 X0
       have i₂ := eq72850
       grind)
    | exact superpose eq72850 eq20583
    | exact resolve eq20583 eq72850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20583
  have eq73315 : ∀ X0 : G, (M.op X0 (M.op x (σ y))) = (M.op (M.op X0 (σ y)) x) := by
    intro X0
    first
    | (have i₁ := eq42982 X0
       have i₂ := eq72850
       grind)
    | exact superpose eq72850 eq42982
    | exact resolve eq42982 eq72850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42982
  have eq73977 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) y) y) := by
    first
    | (have i₁ := eq73125
       have i₂ := eq51551 (σ (M.op x y)) x
       grind)
    | exact superpose eq51551 eq73125
    | exact resolve eq73125 eq51551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73125
  have eq73993 : ∀ X0 : G, x = (M.op (M.op (σ X0) (σ (k X0 y))) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq73071 X0
       have i₂ := eq25571 (σ (k X0 y)) (σ X0) (σ y)
       grind)
    | (have i₁ := eq73071 X0
       have i₂ := eq25571 (σ X0) (σ (k X0 y)) (σ y)
       grind)
    | exact superpose eq25571 eq73071
    | (have j0 := eq73071 (M.op (M.op (σ X0) (σ (k X0 y))) (σ y))
       grind)
    | exact resolve eq73071 eq25571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73071
  have eq74220 : (σ (M.op x y)) = (M.op (M.op y (σ (M.op x y))) y) := by
    first
    | (have i₁ := eq73977
       have i₂ := eq14078 (σ (M.op x y)) y
       grind)
    | exact superpose eq14078 eq73977
    | exact resolve eq73977 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73977
  have eq82407 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x (M.op (σ y) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq73161 X0
       have i₂ := eq23135 x X0 (σ y)
       grind)
    | (have i₁ := eq73161 X0
       have i₂ := eq23135 x (σ y) X0
       grind)
    | exact superpose eq23135 eq73161
    | exact resolve eq73161 eq23135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23135 eq73161
  have eq83562 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op x (M.op x (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq82407 (M.op X0 (σ y))
       have i₂ := eq26759 x X0 (σ y)
       grind)
    | exact superpose eq26759 eq82407
    | exact resolve eq82407 eq26759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82407
  have eq83620 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq83562 X0
       have i₂ := eq51551 X0 x
       grind)
    | exact superpose eq51551 eq83562
    | exact resolve eq83562 eq51551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51551 eq83562
  have eq111209 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) (M.op x (M.op X1 (M.op X0 x)))) ∨ (M.op (M.op X1 (M.op X0 x)) x) = (k (M.op X1 (M.op X0 x)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq28161 X0 X1 (M.op x (M.op X1 (M.op X0 x)))
       have i₂ := eq20734 (M.op X1 (M.op X0 x))
       grind)
    | exact superpose eq20734 eq28161
    | (have j1 := eq20734 (M.op X1 (M.op X0 x))
       grind)
    | exact resolve eq28161 eq20734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20734
  have eq111291 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op X1 x) (M.op X1 (M.op X0 x)))) ∨ (M.op (M.op X1 (M.op X0 x)) x) = (k (M.op X1 (M.op X0 x)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq111209 X0 X1
       have i₂ := eq40108 X0 X1 x (M.op X1 (M.op X0 x))
       grind)
    | exact superpose eq40108 eq111209
    | (have j0 := eq111209 X0 X1
       grind)
    | exact resolve eq111209 eq40108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111209
  have eq111390 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X1 x) X1) x) ∨ (M.op (M.op X1 (M.op X0 x)) x) = (k (M.op X1 (M.op X0 x)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq111291 X0 X1
       have i₂ := eq43947 (M.op X1 x) X1 X0 x
       grind)
    | exact superpose eq43947 eq111291
    | (have j0 := eq111291 X0 X1
       grind)
    | exact resolve eq111291 eq43947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43947 eq111291
  have eq111456 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op X1 x)) x) ∨ (M.op (M.op X1 (M.op X0 x)) x) = (k (M.op X1 (M.op X0 x)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq111390 X0 X1
       have i₂ := eq25571 (M.op X1 x) X1 x
       grind)
    | (have i₁ := eq111390 X0 X1
       have i₂ := eq25571 X1 (M.op X1 x) x
       grind)
    | exact superpose eq25571 eq111390
    | (have j0 := eq111390 X0 X1
       grind)
    | exact resolve eq111390 eq25571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111390
  have eq111498 : ∀ X0 X1 : G, x = (M.op (M.op X1 X1) x) ∨ (M.op (M.op X1 (M.op X0 x)) x) = (k (M.op X1 (M.op X0 x)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq111456 X0 X1
       have i₂ := eq28161 X1 X1 x
       grind)
    | exact superpose eq28161 eq111456
    | (have j0 := eq111456 X0 X1
       grind)
    | exact resolve eq111456 eq28161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111456
  have eq111522 : ∀ X0 X1 : G, x = (M.op x x) ∨ (M.op (M.op X1 (M.op X0 x)) x) = (k (M.op X1 (M.op X0 x)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq111498 X0 X1
       have i₂ := eq21129 X1 x
       grind)
    | exact superpose eq21129 eq111498
    | (have j0 := eq111498 X0 X1
       grind)
    | exact resolve eq111498 eq21129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111498
  have eq111537 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 x)) x) = (k (M.op X1 (M.op X0 x)) x) := by
    intro X0 X1
    first
    | (have j0 := eq111522 X0 X1
       have j1 := eq12 (M.op X1 (M.op X0 x)) x
       grind)
    | (have r₁ := eq111522 X0 X1
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq111522 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111522
  have eq111548 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (k (M.op X1 (M.op X0 x)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq111537 X0 X1
       have i₂ := eq28161 X0 X1 x
       grind)
    | exact superpose eq28161 eq111537
    | exact resolve eq111537 eq28161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28161 eq111537
  have eq111716 : (k y x) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq111548 y x
       have i₂ := eq6121
       grind)
    | exact superpose eq6121 eq111548
    | exact resolve eq111548 eq6121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111718 : (M.op (M.op (σ y) x) x) = (k (σ y) x) := by
    first
    | (have i₁ := eq111548 (σ y) x
       have i₂ := eq73104
       grind)
    | exact superpose eq73104 eq111548
    | exact resolve eq111548 eq73104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111548
  have eq111773 : (σ (k y x)) = (M.op (M.op (σ y) x) x) := by
    first
    | (have i₁ := eq111718
       have i₂ := eq72851 y
       grind)
    | exact superpose eq72851 eq111718
    | exact resolve eq111718 eq72851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72851 eq111718
  have eq111775 : (M.op (M.op x y) x) = (k y x) := by
    first
    | (have i₁ := eq111716
       have i₂ := eq25571 y x x
       grind)
    | (have i₁ := eq111716
       have i₂ := eq25571 x y x
       grind)
    | exact superpose eq25571 eq111716
    | exact resolve eq111716 eq25571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111716
  have eq111890 : (σ (k y x)) = (M.op (M.op x (σ y)) x) := by
    first
    | (have i₁ := eq111773
       have i₂ := eq25571 (σ y) x x
       grind)
    | (have i₁ := eq111773
       have i₂ := eq25571 x (σ y) x
       grind)
    | exact superpose eq25571 eq111773
    | exact resolve eq111773 eq25571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111773
  have eq111892 : (k y x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq111775
       have i₂ := eq24711 x
       grind)
    | exact superpose eq24711 eq111775
    | exact resolve eq111775 eq24711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24711 eq111775
  have eq111975 : (σ (k y x)) = (M.op x (M.op x (σ y))) := by
    first
    | (have i₁ := eq111890
       have i₂ := eq73315 x
       grind)
    | exact superpose eq73315 eq111890
    | exact resolve eq111890 eq73315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73315 eq111890
  have eq111977 : (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq111892
       have i₂ := eq14081 x
       grind)
    | exact superpose eq14081 eq111892
    | exact resolve eq111892 eq14081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111892
  have eq112011 : (σ (k y x)) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq111975
       have i₂ := eq73137 x
       grind)
    | exact superpose eq73137 eq111975
    | exact resolve eq111975 eq73137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73137 eq111975
  have eq112498 : (σ (M.op y x)) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq112011
       have i₂ := eq111977
       grind)
    | exact superpose eq111977 eq112011
    | exact resolve eq112011 eq111977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111977 eq112011
  have eq116695 : ∀ X0 : G, (M.op (M.op (M.op y y) y) y) = (k (M.op (M.op y y) y) y) ∨ y = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq68077 (M.op X0 (M.op X0 x))
       have i₂ := eq47651 X0 y
       grind)
    | exact superpose eq47651 eq68077
    | (have j0 := eq68077 (M.op X0 (M.op X0 x))
       grind)
    | exact resolve eq68077 eq47651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47651 eq68077
  have eq116721 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op x y) y) ∨ y = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq116695 X0
       have i₂ := eq21129 y y
       grind)
    | exact superpose eq21129 eq116695
    | (have j0 := eq116695 X0
       grind)
    | exact resolve eq116695 eq21129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21129 eq116695
  have eq116748 : ∀ X0 : G, (M.op y y) = (k (M.op x y) y) ∨ y = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq116721 X0
       have i₂ := eq14152 y y
       grind)
    | exact superpose eq14152 eq116721
    | (have j0 := eq116721 X0
       grind)
    | exact resolve eq116721 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116721
  have eq116761 : ∀ X0 : G, x = (k (M.op x y) y) ∨ y = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq116748 X0
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq116748
    | (have j0 := eq116748 X0
       grind)
    | exact resolve eq116748 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116748
  have eq147801 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14877 x x
       have i₂ := eq116761 x
       grind)
    | exact superpose eq116761 eq14877
    | exact resolve eq14877 eq116761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14877 eq116761
  have eq212036 : (M.op y (τ (M.op x (τ y)))) = (M.op x (M.op (τ (M.op x (τ y))) y)) := by
    first
    | (have i₁ := eq23010 y (τ (M.op x (τ y))) y
       have i₂ := eq72033
       grind)
    | exact superpose eq72033 eq23010
    | exact resolve eq23010 eq72033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23010
  have eq212039 : (M.op y x) = (M.op (M.op y (τ (M.op x (τ y)))) (τ (M.op x (τ y)))) := by
    first
    | (have i₁ := eq14081 (M.op y (τ (M.op x (τ y))))
       have i₂ := eq72033
       grind)
    | exact superpose eq72033 eq14081
    | exact resolve eq14081 eq72033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14081
  have eq212047 : ∀ X0 : G, (M.op X0 (τ (M.op x (τ y)))) = (M.op (M.op X0 (τ (M.op x (τ y)))) x) := by
    intro X0
    first
    | (have i₁ := eq52114 X0 (M.op y (τ (M.op x (τ y))))
       have i₂ := eq72033
       grind)
    | exact superpose eq72033 eq52114
    | exact resolve eq52114 eq72033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52114 eq72033
  have eq212472 : x = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73993 (M.op x y)
       have i₂ := eq147801
       grind)
    | exact superpose eq147801 eq73993
    | (have j0 := eq73993 (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))
       grind)
    | exact resolve eq73993 eq147801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73993 eq147801
  have eq212558 : x = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq212472
  have eq212608 : x = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212558
       have i₂ := eq25571 (σ (M.op x y)) (σ x) (σ y)
       grind)
    | (have i₁ := eq212558
       have i₂ := eq25571 (σ x) (σ (M.op x y)) (σ y)
       grind)
    | exact superpose eq25571 eq212558
    | exact resolve eq212558 eq25571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25571 eq212558
  have eq212644 : x = (M.op (M.op x (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212608
       have i₂ := eq72850
       grind)
    | exact superpose eq72850 eq212608
    | exact resolve eq212608 eq72850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212608
  have eq212663 : x = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212644
       have i₂ := eq14152 (σ (M.op x y)) (σ y)
       grind)
    | exact superpose eq14152 eq212644
    | exact resolve eq212644 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212644
  have eq212711 : (M.op x (σ y)) = (M.op (M.op (σ (M.op x y)) y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83620 (σ (M.op x y))
       have i₂ := eq212663
       grind)
    | exact superpose eq212663 eq83620
    | exact resolve eq83620 eq212663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83620 eq212663
  have eq212757 : (M.op x (σ y)) = (M.op (M.op y (σ (M.op x y))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212711
       have i₂ := eq14078 (σ (M.op x y)) y
       grind)
    | exact superpose eq14078 eq212711
    | exact resolve eq212711 eq14078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14078 eq212711
  have eq212776 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212757
       have i₂ := eq74220
       grind)
    | exact superpose eq74220 eq212757
    | exact resolve eq212757 eq74220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74220 eq212757
  have eq212780 : x = (M.op x y) := by
    first
    | (have r₁ := eq212776
       have r₂ := eq14385
       grind)
    | exact resolve eq212776 eq14385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212776
  have eq212811 : (σ x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14385
       have i₂ := eq212780
       grind)
    | exact superpose eq212780 eq14385
    | exact resolve eq14385 eq212780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14385
  have eq212830 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) y) = (M.op X1 (M.op X0 (M.op X2 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52974 X0 X1 X2
       have i₂ := eq212780
       grind)
    | exact superpose eq212780 eq52974
    | exact resolve eq52974 eq212780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52974
  have eq214116 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op X0 x))) = (M.op x (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq51607 X0 X1
       have i₂ := eq212830 y X1 X0
       grind)
    | exact superpose eq212830 eq51607
    | exact resolve eq51607 eq212830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51607 eq212830
  have eq214119 : x ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq212811
       have i₂ := eq72850
       grind)
    | exact superpose eq72850 eq212811
    | exact resolve eq212811 eq72850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72850 eq212811
  have eq214277 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op x (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq214116 X0 X1
       have i₂ := eq40723 X0 X1
       grind)
    | exact superpose eq40723 eq214116
    | exact resolve eq214116 eq40723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40723 eq214116
  have eq214362 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) y)) = (M.op (M.op X1 (M.op X2 X0)) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52191 X0 X1 X2
       have i₂ := eq214277 X2 X1
       grind)
    | exact superpose eq214277 eq52191
    | exact resolve eq52191 eq214277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52191 eq214277
  have eq214486 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op (M.op X0 y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq29716 X0 X1
       have i₂ := eq214362 X1 X0 y
       grind)
    | exact superpose eq214362 eq29716
    | exact resolve eq29716 eq214362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29716 eq214362
  have eq214516 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X1 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq214486 X0 X1
       have i₂ := eq47907 X0 X1
       grind)
    | exact superpose eq47907 eq214486
    | exact resolve eq214486 eq47907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47907 eq214486
  have eq214855 : ∀ X0 : G, (M.op X0 (τ (M.op x (τ y)))) = (M.op X0 (M.op (τ (M.op x (τ y))) y)) := by
    intro X0
    first
    | (have i₁ := eq212047 X0
       have i₂ := eq214516 (τ (M.op x (τ y))) X0
       grind)
    | exact superpose eq214516 eq212047
    | exact resolve eq212047 eq214516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212047 eq214516
  have eq214906 : (M.op y (τ (M.op x (τ y)))) = (M.op x (τ (M.op x (τ y)))) := by
    first
    | (have i₁ := eq212036
       have i₂ := eq214855 x
       grind)
    | exact superpose eq214855 eq212036
    | exact resolve eq212036 eq214855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212036 eq214855
  have eq215196 : (M.op y x) = (M.op (M.op x (τ (M.op x (τ y)))) (τ (M.op x (τ y)))) := by
    first
    | (have i₁ := eq212039
       have i₂ := eq214906
       grind)
    | exact superpose eq214906 eq212039
    | exact resolve eq212039 eq214906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212039 eq214906
  have eq215320 : (M.op y x) = (M.op (τ (M.op x (τ y))) (τ (M.op x (τ y)))) := by
    first
    | (have i₁ := eq215196
       have i₂ := eq14152 (τ (M.op x (τ y))) (τ (M.op x (τ y)))
       grind)
    | exact superpose eq14152 eq215196
    | exact resolve eq215196 eq14152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14152 eq215196
  have eq215347 : (M.op y x) = (τ (M.op (M.op x (τ y)) (M.op x (τ y)))) := by
    first
    | (have i₁ := eq215320
       have i₂ := eq944 (M.op x (τ y))
       grind)
    | exact superpose eq944 eq215320
    | exact resolve eq215320 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215320
  have eq215563 : (M.op y x) = (τ (M.op x (M.op (M.op (τ y) x) (τ y)))) := by
    first
    | (have i₁ := eq215347
       have i₂ := eq40108 x (τ y) x (τ y)
       grind)
    | exact superpose eq40108 eq215347
    | exact resolve eq215347 eq40108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40108 eq215347
  have eq215573 : (M.op y x) = (τ (M.op x (M.op (τ y) (τ y)))) := by
    first
    | (have i₁ := eq215563
       have i₂ := eq26759 (τ y) (τ y) x
       grind)
    | exact superpose eq26759 eq215563
    | exact resolve eq215563 eq26759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26759 eq215563
  have eq215576 : (M.op y x) = (M.op x (τ (M.op (τ y) (τ y)))) := by
    first
    | (have i₁ := eq215573
       have i₂ := eq37922 (τ y)
       grind)
    | exact superpose eq37922 eq215573
    | exact resolve eq215573 eq37922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37922 eq215573
  have eq215578 : (M.op y x) = (M.op x (τ (τ (M.op y y)))) := by
    first
    | (have i₁ := eq215576
       have i₂ := eq944 y
       grind)
    | exact superpose eq944 eq215576
    | exact resolve eq215576 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq215576
  have eq215579 : (M.op y x) = (M.op x (τ (τ x))) := by
    first
    | (have i₁ := eq215578
       have i₂ := eq5261
       grind)
    | exact superpose eq5261 eq215578
    | exact resolve eq215578 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261 eq215578
  have eq215580 : (M.op y x) = (M.op x (τ x)) := by
    first
    | (have i₁ := eq215579
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq215579
    | exact resolve eq215579 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215579
  have eq215581 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq215580
       have i₂ := eq69513
       grind)
    | exact superpose eq69513 eq215580
    | exact resolve eq215580 eq69513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69513 eq215580
  have eq215586 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq6121
       have i₂ := eq215581
       grind)
    | exact superpose eq215581 eq6121
    | exact resolve eq6121 eq215581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6121
  have eq215819 : (σ (M.op x x)) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq112498
       have i₂ := eq215581
       grind)
    | exact superpose eq215581 eq112498
    | exact resolve eq112498 eq215581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112498 eq215581
  have eq217292 : (M.op x x) = (M.op (σ y) x) := by
    first
    | (have i₁ := eq215819
       have i₂ := eq71197
       grind)
    | exact superpose eq71197 eq215819
    | exact resolve eq215819 eq71197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71197 eq215819
  have eq218403 : (σ y) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq73104
       have i₂ := eq217292
       grind)
    | exact superpose eq217292 eq73104
    | exact resolve eq73104 eq217292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73104 eq217292
  have eq220033 : y = (σ y) := by
    first
    | (have i₁ := eq218403
       have i₂ := eq215586
       grind)
    | exact superpose eq215586 eq218403
    | exact resolve eq218403 eq215586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215586 eq218403
  have eq227071 : x ≠ (M.op x y) := by
    first
    | (have i₁ := eq214119
       have i₂ := eq220033
       grind)
    | exact superpose eq220033 eq214119
    | exact resolve eq214119 eq220033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214119 eq220033
  have eq232668 : False := by grind
  exact eq232668

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyx_pyx_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (M.op (M.op X2 X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) (M.op (M.op X2 X3) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq56 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq56 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq57 (σ X0)
       grind)
    | exact superpose eq57 eq15
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq57 (τ X0)
       grind)
    | exact superpose eq57 eq18
    | exact resolve eq18 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq65
    | exact resolve eq65 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq65
  have eq82 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X2) X2) x
       have i₂ := eq19 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X2 x
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq190 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op (M.op X2 X3) X3)) (M.op (M.op X2 X4) X4))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X0 (M.op (M.op X2 X3) X3)) X1 X2 X4
       have i₂ := eq141 X0 X2 X3
       grind)
    | exact superpose eq141 eq20
    | exact resolve eq20 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq141
  have eq395 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq427 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq395
  have eq431 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq427 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq427 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq427 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq435 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq431 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq431
    | (have j0 := eq431 X0 X1
       grind)
    | exact resolve eq431 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq431
  have eq715 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq435
    | exact resolve eq435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq435 (σ X1) X0
       grind)
    | exact superpose eq435 eq15
    | (have j1 := eq435 (σ X1) X0
       grind)
    | exact resolve eq15 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq736 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq725
    | (have j0 := eq725 X0 X1
       grind)
    | exact resolve eq725 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq750 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq715 (τ X0) X1
       grind)
    | exact superpose eq715 eq18
    | (have j1 := eq715 (τ X0) X1
       grind)
    | exact resolve eq18 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq715
  have eq5604 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq750 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq750
    | exact resolve eq750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq5686 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5604 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5604
    | (have j0 := eq5604 X0 X1
       grind)
    | exact resolve eq5604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5604
  have eq16493 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq736 x y
       grind)
    | exact superpose eq736 eq16
    | (have j1 := eq736 x y
       grind)
    | exact resolve eq16 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq16883 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16493
       have i₂ := eq5686 x y
       grind)
    | exact superpose eq5686 eq16493
    | (have j1 := eq5686 x y
       grind)
    | (have r₁ := eq16493
       have r₂ := eq5686 x y
       grind)
    | exact resolve eq16493 eq5686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5686 eq16493
  have eq16884 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq16883
  have eq16906 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ y) X0) X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq16884
       grind)
    | exact superpose eq16884 eq9
    | exact resolve eq9 eq16884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16884
  have eq16952 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16906 x
       have i₂ := eq82 y x
       grind)
    | exact superpose eq82 eq16906
    | exact resolve eq16906 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq16906
  have eq17281 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16952
       grind)
    | exact superpose eq16952 eq10
    | exact resolve eq10 eq16952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16952
  have eq17359 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq17281
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17281
    | exact resolve eq17281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17281
  have eq17364 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq16
    | exact resolve eq16 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17359
  have eq17365 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq17364
       have r₂ := eq68 x
       grind)
    | exact resolve eq17364 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17364
  have eq17572 : ∀ X0 X1 X2 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq190 y y X0 X1 X2
       have i₂ := eq17365
       grind)
    | exact superpose eq17365 eq190
    | exact resolve eq190 eq17365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17365
  have eq17601 : x = y := by
    first
    | (have i₁ := eq17572 x x x
       have i₂ := eq190 y x x x x
       grind)
    | exact superpose eq190 eq17572
    | exact resolve eq17572 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq17572
  have eq17619 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17601
       grind)
    | exact superpose eq17601 eq16
    | exact resolve eq16 eq17601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17601
  have eq17622 : False := by grind
  exact eq17622
