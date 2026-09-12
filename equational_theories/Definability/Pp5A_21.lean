import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (M.op X1 X0) X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X2 X0)
       have i₂ := eq43 X2 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq45 (M.op X0 X0) X1
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq135 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq54
    | exact resolve eq54 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq139 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq45 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq45
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq327 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100 x y
       grind)
    | exact superpose eq100 eq16
    | (have j1 := eq100 x y
       grind)
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq6644 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq327
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq327
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq327
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq327
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq327 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq6645 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq6644
  have eq57082 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6645
       grind)
    | exact superpose eq6645 eq16
    | exact resolve eq16 eq6645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6645
  have eq57083 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq57082
       have r₂ := eq135 x (σ x)
       grind)
    | exact resolve eq57082 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57082
  have eq973996 : (σ x) = (M.op (σ y) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45 (σ y) (σ x)
       have i₂ := eq57083
       grind)
    | exact superpose eq57083 eq45
    | exact resolve eq45 eq57083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq57083
  have eq974022 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq973996
       have i₂ := eq139 y
       grind)
    | exact superpose eq139 eq973996
    | exact resolve eq973996 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq973996
  have eq974023 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq974022
  have eq974041 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq974023
       grind)
    | exact superpose eq974023 eq10
    | exact resolve eq10 eq974023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974023
  have eq974305 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq974041
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq974041
    | exact resolve eq974041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974041
  have eq974307 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq974305
       grind)
    | exact superpose eq974305 eq16
    | exact resolve eq16 eq974305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974305
  have eq974308 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq974307
       have r₂ := eq135 x (σ x)
       grind)
    | exact resolve eq974307 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974307
  have eq975863 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq49 y X0 y
       have i₂ := eq974308
       grind)
    | exact superpose eq974308 eq49
    | exact resolve eq49 eq974308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974308
  have eq975873 : x = y := by
    first
    | (have i₁ := eq975863 x
       have i₂ := eq49 y x x
       grind)
    | exact superpose eq49 eq975863
    | exact resolve eq975863 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq975863
  have eq975880 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq975873
       grind)
    | exact superpose eq975873 eq16
    | exact resolve eq16 eq975873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975873
  have eq975881 : False := by grind
  exact eq975881

/-- `Equation2778`: `x = ((y ◇ z) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation2778 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2778 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2778.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq252 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq275 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq276 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq280 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq276 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq276 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq290 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq295 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290
    | exact resolve eq290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq290 x y
       grind)
    | exact superpose eq290 eq16
    | exact resolve eq16 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq377 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq295 X0 (τ X1)
       grind)
    | exact superpose eq295 eq17
    | exact resolve eq17 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq295
  have eq395 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq377
    | exact resolve eq377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq403 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq395
    | exact resolve eq395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq415 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq306
       have i₂ := eq403 x y
       grind)
    | exact superpose eq403 eq306
    | exact resolve eq306 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq403
  have eq416 : False := by grind
  exact eq416

/-- `Equation2883`: `x = ((x ◇ (y ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyy_pxy_Equation2883 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2883 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2883.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) X0) x) = X0 := by
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
  have eq57 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X0 (M.op X2 X3)) X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 (M.op X2 X3)) X0) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X0) X1 X2
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq72
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq89 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq211 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op x y) X1)) X0)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op (M.op X0 (M.op sF0 x)) X0)
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X0 (M.op x y)) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, x ≠ X0 ∨ (M.op (M.op X0 (M.op x y)) X0) = (k x (M.op (M.op X0 (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq56 eq13
    | (have j0 := eq13 x (M.op (M.op X0 (M.op x y)) X0)
       grind)
    | (have r₁ := eq13 x (M.op (M.op x (M.op x y)) x)
       have r₂ := eq56 x
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq215 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) X0)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op (M.op X0 (M.op sF4 x)) X0)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X0 (M.op (σ x) (σ y))) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) x) (M.op (M.op y (M.op X0 X1)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 y x X0 X1
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (M.op X0 X1)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq58
    | (have j0 := eq58 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq58 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) (M.op (M.op X2 X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X2 X1 (M.op (M.op X0 (M.op x x)) X0) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X1) (M.op X0 (M.op (M.op X0 X2) X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op (M.op X0 X2) X0) X1 (M.op X2 (M.op x x)) X2
       have i₂ := eq58 X2 X0 x x
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X1 (M.op (M.op X1 X0) X1)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 (M.op X1 X0) X1 (M.op (M.op X0 (M.op X2 x)) X0)
       have i₂ := eq58 X0 X1 X2 x
       grind)
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) (M.op X0 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 (M.op X0 (M.op (M.op X0 X1) X2)) X0
       have i₂ := eq59 X0 X0 X1 X2
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) (M.op X3 X4)) (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) X0 X3 X4
       have i₂ := eq59 X0 X0 X1 X2
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq785 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq13 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq791 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq785 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq792 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq787 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq787 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq787 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq787 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq793 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq791 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq791 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq791 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq791 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq802 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq792 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq792
    | (have j0 := eq792 X0 X1
       grind)
    | exact resolve eq792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq803 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq793 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq793
    | (have j0 := eq793 X0 X1
       grind)
    | exact resolve eq793 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq961 : x = (M.op (M.op (M.op x y) x) (M.op (M.op y (M.op x y)) y)) := by
    first
    | (have i₁ := eq213 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq213
    | (have j0 := eq213 y x
       grind)
    | exact resolve eq213 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (M.op x y)) (σ y))) := by
    first
    | exact superpose eq26 eq213
    | (have j0 := eq213 (σ y) (σ x)
       grind)
    | exact resolve eq213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 : G, (M.op (M.op (M.op X0 x) X0) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq961 eq14
    | exact resolve eq14 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq998 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq962 eq14
    | exact resolve eq14 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1083 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq998 eq217
    | exact resolve eq217 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq385 (M.op (M.op X0 (M.op x x)) X0) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq385
    | exact resolve eq385 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op (M.op X0 (M.op (M.op X0 x) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq385 eq59
    | exact resolve eq59 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq1143 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq386 (M.op (M.op X0 (M.op x x)) X0) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq386
    | exact resolve eq386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (M.op (M.op X0 (M.op (M.op X0 (σ x)) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq386 eq59
    | exact resolve eq59 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq1216 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq987 eq394
    | exact resolve eq394 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq998 eq394
    | exact resolve eq394 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3403 : (M.op (M.op x (M.op x y)) x) = (k x (M.op (M.op x (M.op x y)) x)) := by
    first
    | (have j0 := eq214 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq3931 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op X0 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq394 X1 (M.op X0 (M.op (M.op X0 X2) X0)) X0
       have i₂ := eq398 X0 X0 X2
       grind)
    | exact superpose eq398 eq394
    | exact resolve eq394 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq4058 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X0 X1) X2)) = (M.op X0 (M.op (M.op X0 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq394 X3 (M.op X0 (M.op (M.op X0 X1) X2)) X0
       have i₂ := eq678 X0 X1 X2
       grind)
    | exact superpose eq678 eq394
    | exact resolve eq394 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4063 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) X2) X3)) X0 X1
       have i₂ := eq678 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq678 eq14
    | exact resolve eq14 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4896 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq92 eq12
    | (have j0 := eq12 (σ y) (σ X0)
       have j1 := eq92 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ X0)
       have r₂ := eq92 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ y)
       have r₂ := eq92 X0
       grind)
    | exact resolve eq12 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4915 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq92 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq4916 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896
  have eq4919 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4916 X0
       have j1 := eq12 (σ y) (σ X0)
       grind)
    | (have r₁ := eq4916 X0
       have r₂ := eq12 (σ X0) (σ y)
       grind)
    | (have r₁ := eq4916 X0
       have r₂ := eq12 (σ y) (σ X0)
       grind)
    | exact resolve eq4916 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916
  have eq4939 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq4919
    | (have j0 := eq4919 X0
       grind)
    | exact resolve eq4919 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4919
  have eq10684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq10685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq10684
    | exact resolve eq10684 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10684
  have eq10696 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq10685
       have r₂ := eq27
       grind)
    | exact resolve eq10685 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10685
  have eq10698 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq10696
    | exact resolve eq10696 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10696
  have eq10703 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq10698 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq10698
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10698
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10698
       grind)
    | exact resolve eq13 eq10698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10698
  have eq10728 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq10703
  have eq11100 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq10728 eq55
    | exact resolve eq55 eq10728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10728
  have eq11126 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq11100
    | exact resolve eq11100 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11100
  have eq11129 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq11126
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq11126
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq11126
       have r₂ := eq13 x y
       grind)
    | exact resolve eq11126 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11126
  have eq11141 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq802 x y
       have i₂ := eq11129
       grind)
    | exact superpose eq11129 eq802
    | (have j0 := eq802 x y
       grind)
    | exact resolve eq802 eq11129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11129
  have eq11144 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11141
  have eq11150 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11144
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq11144
    | exact resolve eq11144 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq11144
  have eq11163 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11150
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11150
    | exact resolve eq11150 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11150
  have eq11167 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11163
       have r₂ := eq51
       grind)
    | exact resolve eq11163 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11163
  have eq11172 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11167
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11167
    | exact resolve eq11167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11167
  have eq11175 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11172
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11172
    | exact resolve eq11172 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11172
  have eq11426 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) (M.op (M.op X3 X4) X5)) (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq59 (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) X3 X4 X5
       have i₂ := eq679 X0 X1 X2 (M.op X3 X4) X5
       grind)
    | exact superpose eq679 eq59
    | exact resolve eq59 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11428 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) (M.op (M.op (σ x) (σ y)) X3)) (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq215 (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) x
       have i₂ := eq679 X0 X1 X2 sF4 x
       grind)
    | exact superpose eq679 eq215
    | exact resolve eq215 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11432 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) (M.op X3 X4)) (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0)) = (M.op X0 (M.op (M.op X3 X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq668 (M.op X3 X4) (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) X5
       have i₂ := eq679 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq679 eq668
    | exact resolve eq668 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq11720 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11175 eq99
    | exact resolve eq99 eq11175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11175
  have eq11744 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq11720
    | exact resolve eq11720 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11720
  have eq11746 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq11744
       have r₂ := eq50
       grind)
    | exact resolve eq11744 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11744
  have eq11840 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq11746 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq11746
       grind)
    | exact resolve eq13 eq11746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11746
  have eq11870 : (σ y) = (k (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq11840
  have eq11889 : (τ (σ y)) = (k x y) ∨ x = (k y x) := by
    first
    | exact superpose eq11870 eq55
    | exact resolve eq55 eq11870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11870
  have eq11914 : y = (k x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq11889
    | exact resolve eq11889 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11889
  have eq11930 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq11914
       grind)
    | exact superpose eq11914 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq11914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11914
  have eq11931 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by grind
  clear eq11930
  have eq11936 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq11931
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq11931
       have r₂ := eq13 x y
       grind)
    | exact resolve eq11931 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11931
  have eq12131 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq803 y x
       have i₂ := eq11936
       grind)
    | exact superpose eq11936 eq803
    | (have j0 := eq803 x x
       grind)
    | exact resolve eq803 eq11936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12133 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq802 y x
       have i₂ := eq11936
       grind)
    | exact superpose eq11936 eq802
    | (have j0 := eq802 y x
       grind)
    | exact resolve eq802 eq11936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq12134 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11936
       grind)
    | exact superpose eq11936 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11936
  have eq12135 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq12134
  have eq12136 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq12133
  have eq12138 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq12131
  have eq12140 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12135
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12135
    | exact resolve eq12135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12135
  have eq12141 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12136
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq12136
    | exact resolve eq12136 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq12136
  have eq12143 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12138
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12138
    | exact resolve eq12138 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12138
  have eq12153 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12141
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12141
    | exact resolve eq12141 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12141
  have eq12155 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12143
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12143
    | exact resolve eq12143 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12143
  have eq12157 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12153
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12153
    | exact resolve eq12153 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12153
  have eq12159 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12155
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12155
    | exact resolve eq12155 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12155
  have eq12161 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12157
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12157
    | exact resolve eq12157 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12157
  have eq12163 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq12159
    | exact resolve eq12159 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12159
  have eq12165 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq12161
    | exact resolve eq12161 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12161
  have eq12170 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1099 x
       have i₂ := eq12140
       grind)
    | exact superpose eq12140 eq1099
    | exact resolve eq1099 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq12171 : y = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq987 y
       have i₂ := eq12140
       grind)
    | exact superpose eq12140 eq987
    | exact resolve eq987 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12172 : x ≠ x ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq12140
       grind)
    | exact superpose eq12140 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12140
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12140
       grind)
    | exact resolve eq12 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12189 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq394 X0 y x
       have i₂ := eq12140
       grind)
    | exact superpose eq12140 eq394
    | exact resolve eq394 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12190 : ∀ X0 : G, (M.op (M.op (M.op X0 y) X0) (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq394 x X0 y
       have i₂ := eq12140
       grind)
    | exact superpose eq12140 eq394
    | exact resolve eq394 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12140
  have eq12205 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq12172
  have eq12210 : ∀ X0 : G, (M.op (M.op (M.op X0 y) X0) (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12190 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12190
    | (have j0 := eq12190 X0
       grind)
    | exact resolve eq12190 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12190
  have eq12211 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12189 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12189
    | (have j0 := eq12189 X0
       grind)
    | exact resolve eq12189 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12189
  have eq12216 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12205
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12205
    | exact resolve eq12205 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12205
  have eq12217 : (k y x) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq12216
  have eq12218 : y = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12171
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12171
    | exact resolve eq12171 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12171
  have eq12219 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12170
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12170
    | exact resolve eq12170 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12170
  have eq13933 : (M.op x y) = (M.op x (M.op (M.op x (M.op x y)) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12219 eq213
    | exact resolve eq213 eq12219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13936 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x X0) x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12219 eq394
    | exact resolve eq394 eq12219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12219
  have eq18450 : ∀ X0 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13933 eq668
    | exact resolve eq668 eq13933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13933
  have eq18712 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x X0) x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 x X1
       have i₂ := eq13936 X0
       grind)
    | exact superpose eq13936 eq668
    | exact resolve eq668 eq13936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13936
  have eq21230 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12165 eq55
    | exact resolve eq55 eq12165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq12165
  have eq21261 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq21230
    | exact resolve eq21230 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21230
  have eq21266 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq21261
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq21261
       have r₂ := eq13 x y
       grind)
    | exact resolve eq21261 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21261
  have eq21281 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq788 x y
       have i₂ := eq21266
       grind)
    | exact superpose eq21266 eq788
    | (have j0 := eq788 x y
       grind)
    | exact resolve eq788 eq21266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq21266
  have eq21286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21281
  have eq21291 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21286
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21286
    | exact resolve eq21286 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21286
  have eq21306 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21291
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21291
    | exact resolve eq21291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21291
  have eq21312 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21306
    | exact resolve eq21306 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21306
  have eq21313 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq21312
  have eq21318 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21313
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21313
    | exact resolve eq21313 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21313
  have eq21323 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21318
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21318
    | exact resolve eq21318 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21318
  have eq21374 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21323 eq1143
    | exact resolve eq1143 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq21375 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21323 eq998
    | exact resolve eq998 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq21378 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) X0) (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21323 eq14
    | exact resolve eq14 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21393 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21323 eq394
    | exact resolve eq394 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21394 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) X0) (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21323 eq394
    | exact resolve eq394 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21423 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) X0) (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq21394
    | (have j0 := eq21394 X0
       grind)
    | exact resolve eq21394 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21394
  have eq21424 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq21393
    | (have j0 := eq21393 X0
       grind)
    | exact resolve eq21393 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21393
  have eq21431 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21375
    | exact resolve eq21375 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21375
  have eq21432 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21374
    | exact resolve eq21374 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21374
  have eq21503 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21431 eq14
    | exact resolve eq14 eq21431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21561 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (M.op x y)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21432 eq213
    | exact resolve eq213 eq21432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq21562 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21432 eq217
    | exact resolve eq217 eq21432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq21564 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21432 eq394
    | exact resolve eq394 eq21432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21432
  have eq22183 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12163 eq21378
    | exact resolve eq21378 eq12163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12163
  have eq22184 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21323 eq21378
    | exact resolve eq21378 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22188 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq21378 (M.op sF2 (M.op (M.op sF2 X1) x))
       have i₂ := eq678 sF2 X1 x
       grind)
    | exact superpose eq678 eq21378
    | exact resolve eq21378 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq22252 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22184
  have eq22253 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq22183
  have eq22257 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq22188
    | (have j0 := eq22188 X0 X1
       grind)
    | exact resolve eq22188 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22188
  have eq22260 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22252
    | exact resolve eq22252 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22252
  have eq23538 : ∀ X0 : G, (M.op (M.op (σ x) (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21561 eq668
    | exact resolve eq668 eq21561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21561
  have eq23605 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21562 eq668
    | exact resolve eq668 eq21562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21562
  have eq23684 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21564 eq668
    | exact resolve eq668 eq21564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21564
  have eq32655 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12218 eq18450
    | exact resolve eq18450 eq12218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12218
  have eq32663 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) X0))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18450 eq12211
    | exact resolve eq12211 eq18450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12211
  have eq32795 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq32663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32663
  have eq32801 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by grind
  clear eq32655
  have eq33184 : y = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32795 eq18450
    | exact resolve eq18450 eq32795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32795
  have eq33248 : y = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by grind
  clear eq33184
  have eq34251 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32801 eq18450
    | exact resolve eq18450 eq32801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18450 eq32801
  have eq34332 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34251
  have eq35071 : (M.op (M.op (M.op x y) y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) y) (M.op x y))) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34332 eq211
    | exact resolve eq211 eq34332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq34332
  have eq35151 : (M.op (M.op (M.op x y) x) x) = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1216 eq35071
    | exact resolve eq35071 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216 eq35071
  have eq39247 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x y) (M.op (M.op X0 X1) X2)) X0) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 x X0 X1
       have i₂ := eq18712 (M.op X0 X1) X2
       grind)
    | exact superpose eq18712 eq14
    | exact resolve eq14 eq18712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40091 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21323 eq3931
    | exact resolve eq3931 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3931
  have eq40615 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq40091
    | (have j0 := eq40091 X0
       grind)
    | exact resolve eq40091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40091
  have eq44162 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ y) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21323 eq4058
    | exact resolve eq4058 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4058 eq21323
  have eq44729 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ y) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq44162
    | (have j0 := eq44162 X0 X1
       grind)
    | exact resolve eq44162 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44162
  have eq47197 : (M.op (M.op (σ y) (σ x)) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40615 eq1162
    | exact resolve eq1162 eq40615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq40615
  have eq55592 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq39247 (M.op X0 X1) X0 (M.op (M.op X1 x) X1)
       have i₂ := eq394 x X0 X1
       grind)
    | exact superpose eq394 eq39247
    | exact resolve eq39247 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39247
  have eq68508 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47197 eq21503
    | exact resolve eq21503 eq47197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47197
  have eq68590 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq68508
  have eq68963 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq68590 eq4063
    | exact resolve eq4063 eq68590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72506 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23538 eq21424
    | exact resolve eq21424 eq23538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23538
  have eq72692 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq72506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72506
  have eq75632 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21431 eq23605
    | exact resolve eq23605 eq21431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21431
  have eq75753 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23605 eq72692
    | exact resolve eq72692 eq23605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72692
  have eq75843 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq75753
  have eq75854 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq75632
  have eq78276 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq75854 eq23605
    | exact resolve eq23605 eq75854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23605 eq75854
  have eq78386 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq78276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78276
  have eq79266 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y)))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78386 eq215
    | exact resolve eq215 eq78386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq79373 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1217 eq79266
    | exact resolve eq79266 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq79266
  have eq81773 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq23684 eq23684
    | exact resolve eq23684 eq23684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81949 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) X2)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f81949_13 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f81949_19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f81949_21 : (σ x) ≠ (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) X2)) X0) := by grind
    have f81949_22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f81949_23 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) X0) (σ x)) := by
      intro X0 X1
      first
      | (have j0 := f81949_13 X0 X1
         grind)
      | (have r₁ := f81949_13 X0 X1
         have r₂ := f81949_22
         grind)
      | exact resolve f81949_13 f81949_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f81949_65 : (σ x) ≠ (M.op (M.op (M.op (σ x) (M.op X0 X1)) (σ x)) X0) := by
      first
      | (have i₁ := f81949_21
         have i₂ := f81949_23 (M.op X0 X1) X2
         grind)
      | exact superpose f81949_23 f81949_21
      | exact resolve f81949_21 f81949_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f81949_75 : False := by
      first
      | (have r₁ := f81949_65
         have r₂ := f81949_19 (σ x) X0 X1
         grind)
      | exact resolve f81949_65 f81949_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f81949_75
  have eq82124 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq81773 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81773
  have eq116919 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35151 eq12210
    | exact resolve eq12210 eq35151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12210 eq35151
  have eq117022 : (M.op x y) = (M.op (M.op (M.op (M.op x y) x) x) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq116919
  have eq136443 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq81949 (M.op X0 X1) X0 (M.op (M.op X1 x) X1)
       have i₂ := eq394 x X0 X1
       grind)
    | exact superpose eq394 eq81949
    | exact resolve eq81949 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81949
  have eq144737 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ x)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq68963 eq82124
    | exact resolve eq82124 eq68963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68963
  have eq145179 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq82124 eq21424
    | exact resolve eq21424 eq82124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21424 eq82124
  have eq145413 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq145179 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145179
  have eq145569 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ x)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq144737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144737
  have eq195789 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq145569 eq59
    | exact resolve eq59 eq145569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq145569
  have eq195902 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1083 eq195789
    | exact resolve eq195789 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq195789
  have eq204154 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq79373 eq21423
    | exact resolve eq21423 eq79373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204266 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq204154
  have eq221952 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq195902 eq57
    | exact resolve eq57 eq195902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq195902
  have eq271724 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22253 eq22257
    | exact resolve eq22257 eq22253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271728 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22253 eq145413
    | exact resolve eq145413 eq22253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145413
  have eq271835 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq271728
  have eq271837 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq271724
  have eq272074 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq271837 eq22253
    | exact resolve eq22253 eq271837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22253 eq271837
  have eq272246 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq272074
  have eq272916 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq272246 eq78386
    | exact resolve eq78386 eq272246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78386 eq272246
  have eq273042 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq272916
  have eq278520 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq273042 eq221952
    | exact resolve eq221952 eq273042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221952 eq273042
  have eq278713 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq278520
  have eq278770 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq278713
    | exact resolve eq278713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq278713
  have eq286371 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq278770 eq271835
    | exact resolve eq271835 eq278770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271835 eq278770
  have eq286545 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq286371
  have eq286651 : y = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq987 y
       have i₂ := eq286545
       grind)
    | exact superpose eq286545 eq987
    | exact resolve eq987 eq286545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq286663 : ∀ X0 : G, (M.op (M.op (M.op X0 x) X0) y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq286545
       grind)
    | exact superpose eq286545 eq14
    | exact resolve eq14 eq286545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286678 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq394 X0 y x
       have i₂ := eq286545
       grind)
    | exact superpose eq286545 eq394
    | exact resolve eq394 eq286545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq286716 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op x X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq4063 y x x x
       have i₂ := eq286545
       grind)
    | exact superpose eq286545 eq4063
    | exact resolve eq4063 eq286545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063
  have eq286738 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op x X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq286716 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq286716
    | (have j0 := eq286716 X0 X1
       grind)
    | exact resolve eq286716 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286716
  have eq286763 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq286678 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq286678
    | (have j0 := eq286678 X0
       grind)
    | exact resolve eq286678 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286678
  have eq286780 : y = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq286651
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq286651
    | exact resolve eq286651 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286651
  have eq292323 : y = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq286663 y
       have i₂ := eq286545
       grind)
    | exact superpose eq286545 eq286663
    | exact resolve eq286663 eq286545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286545
  have eq292463 : y = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq292323
  have eq292527 : y = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq292463
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq292463
    | exact resolve eq292463 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292463
  have eq293442 : y ≠ y ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq292527 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq292527
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq292527
       grind)
    | exact resolve eq13 eq292527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292527
  have eq293516 : (M.op x y) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq293442
  have eq293593 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq293516 eq4939
    | (have j0 := eq4939 (M.op x y)
       grind)
    | exact resolve eq4939 eq293516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4939
  have eq293594 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq293516 eq4915
    | (have j0 := eq4915 (M.op x y)
       grind)
    | exact resolve eq4915 eq293516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915 eq293516
  have eq293610 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq293594
  have eq293611 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq293593
  have eq293620 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq293610
    | exact resolve eq293610 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293610
  have eq293621 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq293611
    | exact resolve eq293611 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293611
  have eq293645 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq293620
    | exact resolve eq293620 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293620
  have eq293646 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq293621
    | exact resolve eq293621 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293621
  have eq295921 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 x X1
       have i₂ := eq286738 X0 x
       grind)
    | exact superpose eq286738 eq668
    | exact resolve eq668 eq286738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq295944 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1116 x
       have i₂ := eq286738 x x
       grind)
    | exact superpose eq286738 eq1116
    | exact resolve eq1116 eq286738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq286738
  have eq301862 : x = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq286663 x
       have i₂ := eq295944
       grind)
    | exact superpose eq295944 eq286663
    | exact resolve eq286663 eq295944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286663 eq295944
  have eq301996 : x = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq301862
  have eq308323 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq293645 eq21423
    | exact resolve eq21423 eq293645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21423 eq293645
  have eq308406 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq308323
  have eq322750 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq286780 eq295921
    | exact resolve eq295921 eq286780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286780
  have eq323234 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq286763 X0
       have i₂ := eq295921 X0 X1
       grind)
    | exact superpose eq295921 eq286763
    | exact resolve eq286763 eq295921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286763 eq295921
  have eq323568 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq323234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323234
  have eq323683 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq322750
  have eq339140 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq323568 (M.op (M.op X0 (M.op x x)) X0) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq323568
    | exact resolve eq323568 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323568
  have eq369110 : (M.op (M.op x y) y) = (k x (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq323683 eq3403
    | exact resolve eq3403 eq323683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403 eq323683
  have eq511334 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) X3)) (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq79373 eq11426
    | exact resolve eq11426 eq79373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79373
  have eq515577 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq511334 X0 x x x
       have i₂ := eq11426 X0 x x (M.op sF4 sF2) sF2 x
       grind)
    | exact superpose eq11426 eq511334
    | exact resolve eq511334 eq11426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11426 eq511334
  have eq699731 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0)) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq515577 eq11432
    | exact resolve eq11432 eq515577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11432 eq515577
  have eq701065 : ∀ X0 X3 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X3
    first
    | exact superpose eq11428 eq699731
    | exact resolve eq699731 eq11428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11428 eq699731
  have eq719008 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq22260 eq701065
    | exact resolve eq701065 eq22260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22260 eq701065
  have eq720636 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq719008 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719008
  have eq1358892 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq308406 eq44729
    | exact resolve eq44729 eq308406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44729
  have eq1359167 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq1358892
  have eq1375392 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1359167 eq21503
    | exact resolve eq21503 eq1359167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21503 eq1359167
  have eq1375760 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq1375392
  have eq1383594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1375760 eq308406
    | exact resolve eq308406 eq1375760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308406 eq1375760
  have eq1383880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq1383594
  have eq1383956 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1383880
       have r₂ := eq27
       grind)
    | exact resolve eq1383880 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383880
  have eq1384018 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1383956 eq720636
    | exact resolve eq720636 eq1383956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720636
  have eq1384235 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1384018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384018
  have eq1391798 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1384235 eq68590
    | exact resolve eq68590 eq1384235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68590 eq1384235
  have eq1392231 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1391798
  have eq1394306 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1383956 eq1392231
    | exact resolve eq1392231 eq1383956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383956 eq1392231
  have eq1394632 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1394306
  have eq1394727 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1394632 eq293646
    | exact resolve eq293646 eq1394632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293646 eq1394632
  have eq1394968 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1394727
  have eq1395038 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1394968 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq1394968
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1394968
       grind)
    | exact resolve eq13 eq1394968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394968
  have eq1395246 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1395038
  have eq1395286 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1395246 eq152
    | exact resolve eq152 eq1395246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1395246
  have eq1395368 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq1395286
    | exact resolve eq1395286 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1395286
  have eq1395427 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1395368 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq1395368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395368
  have eq1395464 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1395427
  have eq1395636 : x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1395464 eq301996
    | exact resolve eq301996 eq1395464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301996
  have eq1395730 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1395464 eq339140
    | exact resolve eq339140 eq1395464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339140
  have eq1396094 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1395730
  have eq1396133 : x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1395636
  have eq1397221 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1396094 eq1395464
    | exact resolve eq1395464 eq1396094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395464 eq1396094
  have eq1397684 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1397221
  have eq1398047 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1397684 eq51
    | (have r₁ := eq51
       have r₂ := eq1397684
       grind)
    | exact resolve eq51 eq1397684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1397684
  have eq1398333 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1398047
  have eq1399288 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1396133 eq369110
    | exact resolve eq369110 eq1396133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369110 eq1396133
  have eq1399703 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1399288
  have eq1411232 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq803 x x
       have i₂ := eq1399703
       grind)
    | exact superpose eq1399703 eq803
    | (have j0 := eq803 x x
       grind)
    | exact resolve eq803 eq1399703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq1399703
  have eq1411257 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1411232
  have eq1411258 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1411257
  have eq1411288 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1411258
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1411258
    | exact resolve eq1411258 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411258
  have eq1411934 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1398333 eq99
    | exact resolve eq99 eq1398333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1398333
  have eq1412009 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq1411934
    | exact resolve eq1411934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1411934
  have eq1412014 : x = (k y x) := by
    first
    | (have r₁ := eq1412009
       have r₂ := eq50
       grind)
    | exact resolve eq1412009 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1412009
  have eq1412017 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1412014
       have i₂ := eq12217
       grind)
    | exact superpose eq12217 eq1412014
    | exact resolve eq1412014 eq12217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12217 eq1412014
  have eq1414795 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1411288 eq21378
    | exact resolve eq21378 eq1411288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21378
  have eq1414954 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1411288 eq23684
    | exact resolve eq23684 eq1411288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23684
  have eq1414962 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1411288 eq136443
    | exact resolve eq136443 eq1411288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136443 eq1411288
  have eq1415016 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1414962
  have eq1415020 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1414954
  have eq1415029 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1414795
  have eq1417248 : (M.op x x) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18712 x x
       have i₂ := eq1412017
       grind)
    | exact superpose eq1412017 eq18712
    | exact resolve eq18712 eq1412017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18712
  have eq1417252 : x = (M.op (M.op (M.op x y) x) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55592 x x
       have i₂ := eq1412017
       grind)
    | exact superpose eq1412017 eq55592
    | exact resolve eq55592 eq1412017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55592
  have eq1417306 : x = (M.op (M.op (M.op x y) x) x) ∨ y = (M.op x y) := by grind
  clear eq1417252
  have eq1417310 : (M.op x x) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq1417248
  have eq1646346 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1415016 eq204266
    | exact resolve eq204266 eq1415016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204266 eq1415016
  have eq1646663 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1646346
  have eq1646767 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1646663 eq75843
    | exact resolve eq75843 eq1646663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75843 eq1646663
  have eq1647210 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1646767
  have eq1649970 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1415020 eq1647210
    | exact resolve eq1647210 eq1415020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415020 eq1647210
  have eq1650381 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1649970
  have eq1651945 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1415029 eq22257
    | exact resolve eq22257 eq1415029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22257 eq1415029
  have eq1652249 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1651945
  have eq1652599 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1652249 eq1650381
    | exact resolve eq1650381 eq1652249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650381 eq1652249
  have eq1652984 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1652599
  have eq1653062 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1652984 eq27
    | exact resolve eq27 eq1652984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1652984
  have eq1742585 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1417306 eq117022
    | exact resolve eq117022 eq1417306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117022 eq1417306
  have eq1742933 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq1742585
  have eq1743100 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1742933 eq33248
    | exact resolve eq33248 eq1742933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33248 eq1742933
  have eq1743653 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq1743100
  have eq1745922 : y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1417310 eq1743653
    | exact resolve eq1743653 eq1417310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417310 eq1743653
  have eq1746354 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1745922
  have eq1747021 : x = y ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1412017
       have i₂ := eq1746354
       grind)
    | exact superpose eq1746354 eq1412017
    | exact resolve eq1412017 eq1746354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412017
  have eq1747454 : y = (M.op x y) ∨ x = y := by grind
  clear eq1747021
  have eq1747630 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1747454 eq20
    | exact resolve eq20 eq1747454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747454
  have eq1748796 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1747630
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1747630
    | exact resolve eq1747630 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747630
  have eq1748817 : x = y := by
    first
    | (have r₁ := eq1748796
       have r₂ := eq1653062
       grind)
    | exact resolve eq1748796 eq1653062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748796
  have eq1748825 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1748817
       grind)
    | exact superpose eq1748817 eq18
    | exact resolve eq18 eq1748817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1748826 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1748817
       grind)
    | exact superpose eq1748817 eq24
    | exact resolve eq24 eq1748817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1749797 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1748826
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1748826
    | exact resolve eq1748826 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748826
  have eq1750452 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1749797 eq1653062
    | exact resolve eq1653062 eq1749797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653062 eq1749797
  have eq1751588 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1746354
       have i₂ := eq1748825
       grind)
    | exact superpose eq1748825 eq1746354
    | exact resolve eq1746354 eq1748825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746354 eq1748825
  have eq1751961 : y = (M.op x y) := by grind
  clear eq1751588
  have eq1752064 : x = (M.op x y) := by
    first
    | (have i₁ := eq1751961
       have i₂ := eq1748817
       grind)
    | exact superpose eq1748817 eq1751961
    | exact resolve eq1751961 eq1748817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748817 eq1751961
  have eq1752208 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1752064 eq20
    | exact resolve eq20 eq1752064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1752064
  have eq1753714 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1752208
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1752208
    | exact resolve eq1752208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1752208
  have eq1753871 : False := by grind
  exact eq1753871

/-- `Equation2890`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyx_pxy_Equation2890 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2890 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2890.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 (M.op x x)) x) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (M.op X0 X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq361 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq359 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq359 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq359 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq372 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq361 (σ X0)
       grind)
    | exact superpose eq361 eq15
    | exact resolve eq15 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq361 X0
       grind)
    | exact superpose eq361 eq372
    | exact resolve eq372 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq372
  have eq441 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq67
    | exact resolve eq67 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq448 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq441 X0 X1
       have j1 := eq444 X0 X1
       grind)
    | (have r₁ := eq441 X0 X1
       have r₂ := eq444 X0 X1
       grind)
    | exact resolve eq441 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq1005 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq448 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq448
    | exact resolve eq448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1016 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq448 X1 (σ X0)
       grind)
    | exact superpose eq448 eq15
    | (have j1 := eq448 X1 (σ X0)
       grind)
    | exact resolve eq15 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq1056 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1005 X1 (τ X0)
       grind)
    | exact superpose eq1005 eq17
    | (have j1 := eq1005 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1005
  have eq1182 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1056 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1056
    | exact resolve eq1056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1248 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1182 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1182
    | (have j0 := eq1182 X0 X1
       grind)
    | exact resolve eq1182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq2046 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1016 x y
       grind)
    | exact superpose eq1016 eq16
    | (have j1 := eq1016 x y
       grind)
    | exact resolve eq16 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq2165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2046
       have i₂ := eq1248 x y
       grind)
    | exact superpose eq1248 eq2046
    | (have j1 := eq1248 (σ x) (σ y)
       grind)
    | (have r₁ := eq2046
       have r₂ := eq1248 x y
       grind)
    | exact resolve eq2046 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq2046
  have eq2166 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq2165
  have eq2170 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq2166
       grind)
    | exact superpose eq2166 eq61
    | exact resolve eq61 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2177 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2170
       have i₂ := eq2166
       grind)
    | exact superpose eq2166 eq2170
    | exact resolve eq2170 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166 eq2170
  have eq2186 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2177
  have eq2228 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq61 (σ x) (σ y)
       have i₂ := eq2186
       grind)
    | exact superpose eq2186 eq61
    | exact resolve eq61 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2291 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2228
       have i₂ := eq2186
       grind)
    | exact superpose eq2186 eq2228
    | exact resolve eq2228 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186 eq2228
  have eq2302 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2291
  have eq2308 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2302
       have i₂ := eq391 y
       grind)
    | exact superpose eq391 eq2302
    | exact resolve eq2302 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq2318 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq444 y X0
       have i₂ := eq2308
       grind)
    | exact superpose eq2308 eq444
    | (have j0 := eq444 y X0
       grind)
    | (have r₁ := eq444 y x
       have r₂ := eq2308
       grind)
    | exact resolve eq444 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2319 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq446 y
       have i₂ := eq2308
       grind)
    | exact superpose eq2308 eq446
    | exact resolve eq446 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq2308
  have eq2344 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq2318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318
  have eq2352 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2319
       have i₂ := eq391 y
       grind)
    | exact superpose eq391 eq2319
    | exact resolve eq2319 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq2319
  have eq2353 : (σ y) = (σ (M.op y y)) := by grind
  clear eq2352
  have eq2354 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2344 X0
       have j1 := eq444 y X0
       grind)
    | (have r₁ := eq2344 X0
       have r₂ := eq444 y x
       grind)
    | exact resolve eq2344 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq2344
  have eq2370 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2353
       grind)
    | exact superpose eq2353 eq10
    | exact resolve eq10 eq2353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2424 : y = (M.op y y) := by
    first
    | (have i₁ := eq2370
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2370
    | exact resolve eq2370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2441 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2424
       grind)
    | exact superpose eq2424 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq2424
       grind)
    | exact resolve eq12 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2477 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq2441 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq2570 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq2354 (σ X0)
       grind)
    | exact superpose eq2354 eq15
    | exact resolve eq15 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq2590 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2570 X0
       have i₂ := eq2477 X0
       grind)
    | exact superpose eq2477 eq2570
    | exact resolve eq2570 eq2477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477 eq2570
  have eq2643 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2590 x
       grind)
    | exact superpose eq2590 eq16
    | (have r₁ := eq16
       have r₂ := eq2590 x
       grind)
    | exact resolve eq16 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2684 : False := by grind
  exact eq2684

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pyx_pxy_pyx_Equation2982 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq40 X1 X0
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq40 X0 X1
       grind)
    | exact resolve eq48 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq48
  have eq53 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq51
  have eq122 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq270 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X0 (M.op X0 X1) x
       have i₂ := eq20 X0 X0 X1 x
       grind)
    | exact superpose eq20 eq19
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq443 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0
       have i₂ := eq270 X0 X1
       grind)
    | (have i₁ := eq53 X1 X0
       have i₂ := eq270 X1 X0
       grind)
    | exact superpose eq270 eq53
    | (have j0 := eq53 X1 X0
       grind)
    | exact resolve eq53 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq270
  have eq467 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq443 X0 X1
       have j1 := eq122 X1 X0
       grind)
    | (have r₁ := eq443 X0 X0
       have r₂ := eq122 X0 X0
       grind)
    | (have r₁ := eq443 X1 X0
       have r₂ := eq122 X0 X1
       grind)
    | exact resolve eq443 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq443
  have eq1984 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq467 (σ X0) (σ X1)
       grind)
    | exact superpose eq467 eq15
    | exact resolve eq15 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1997 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1984 X0 X1
       have i₂ := eq467 X0 X1
       grind)
    | exact superpose eq467 eq1984
    | exact resolve eq1984 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq1984
  have eq2010 : False := by grind
  exact eq2010

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pxy_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq212 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op sF0 (M.op x X0)) x)
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op sF4 (M.op x X0)) x)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq483 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq482 eq57
    | exact resolve eq57 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq527 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq483 eq57
    | exact resolve eq57 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq849 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X0 (M.op X0 X1) x
       have i₂ := eq56 X0 X0 X1 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq855 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) X3 X1
       have i₂ := eq56 X3 X1 X0 X2
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1076 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq76
  have eq1337 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op y y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1076 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1076
    | (have j0 := eq1076 X0 y
       grind)
    | exact resolve eq1076 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1361 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op y y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1337 X0
       have i₂ := eq853 sF3 (σ X0)
       grind)
    | (have i₁ := eq1337 X0
       have i₂ := eq853 (σ X0) sF3
       grind)
    | exact superpose eq853 eq1337
    | (have j0 := eq1337 X0
       grind)
    | exact resolve eq1337 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1379 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1361 X0
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq1361
    | (have j0 := eq1361 X0
       grind)
    | exact resolve eq1361 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1361
  have eq1846 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq853 X0 (M.op X1 (M.op X2 X0))
       grind)
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq853 (M.op X1 (M.op X2 X0)) X0
       grind)
    | exact superpose eq853 eq481
    | exact resolve eq481 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1891 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq853 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq853 (M.op X1 X2) X0
       grind)
    | exact superpose eq853 eq491
    | exact resolve eq491 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2198 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq849 X0 X1 X2
       have i₂ := eq853 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | (have i₁ := eq849 X0 X1 X2
       have i₂ := eq853 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | exact superpose eq853 eq849
    | exact resolve eq849 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq2482 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2198 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1846 X2 X1 X0
       grind)
    | exact superpose eq1846 eq2198
    | exact resolve eq2198 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq2198
  have eq2619 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X0
       have i₂ := eq853 X0 (M.op sF0 (M.op X0 X0))
       grind)
    | (have i₁ := eq212 X0 X1
       have i₂ := eq853 (M.op sF0 (M.op X1 X0)) X1
       grind)
    | exact superpose eq853 eq212
    | exact resolve eq212 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2704 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X0
       have i₂ := eq853 X0 (M.op sF4 (M.op X0 X0))
       grind)
    | (have i₁ := eq217 X0 X1
       have i₂ := eq853 (M.op sF4 (M.op X1 X0)) X1
       grind)
    | exact superpose eq853 eq217
    | exact resolve eq217 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq853
  have eq4298 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op (M.op x y) (M.op X0 X1))) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq2619 eq57
    | exact resolve eq57 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq4331 : ∀ X0 X1 : G, x = (M.op (M.op X1 y) (M.op (M.op (M.op x y) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4298 x X1
       have i₂ := eq1891 (M.op X1 y) (M.op sF0 (M.op x X1)) x
       grind)
    | exact superpose eq1891 eq4298
    | exact resolve eq4298 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298
  have eq4410 : ∀ X0 X1 : G, x = (M.op (M.op X1 y) (M.op X0 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4331 X0 X1
       have i₂ := eq2482 X0 (M.op X1 y) (M.op sF0 (M.op X0 X1))
       grind)
    | (have i₁ := eq4331 x X1
       have i₂ := eq2482 (M.op sF0 (M.op x X1)) (M.op X1 y) x
       grind)
    | exact superpose eq2482 eq4331
    | exact resolve eq4331 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331
  have eq5225 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2704 eq57
    | exact resolve eq57 eq2704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2704
  have eq5262 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5225 x X1
       have i₂ := eq1891 (M.op X1 sF3) (M.op sF4 (M.op x X1)) x
       grind)
    | exact superpose eq1891 eq5225
    | exact resolve eq5225 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5225
  have eq5349 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ y)) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5262 X0 X1
       have i₂ := eq2482 X0 (M.op X1 sF3) (M.op sF4 (M.op X0 X1))
       grind)
    | (have i₁ := eq5262 x X1
       have i₂ := eq2482 (M.op sF4 (M.op x X1)) (M.op X1 sF3) x
       grind)
    | exact superpose eq2482 eq5262
    | exact resolve eq5262 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5262
  have eq12515 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3))) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq855 X0 X1 X2 X3
       have i₂ := eq491 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq855 X0 X1 X2 X3
       have i₂ := eq491 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq491 eq855
    | exact resolve eq855 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq855
  have eq12516 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12515 X0 X1 X2 X3
       have i₂ := eq1891 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3)) X2
       grind)
    | exact superpose eq1891 eq12515
    | exact resolve eq12515 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891 eq12515
  have eq12517 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12516 X0 X1 X2 X3
       have i₂ := eq2482 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq12516 X0 X1 X2 X3
       have i₂ := eq2482 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq2482 eq12516
    | exact resolve eq12516 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482 eq12516
  have eq75751 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1379 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1379
    | (have j0 := eq1379 x
       grind)
    | exact resolve eq1379 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq75923 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527 eq75751
    | exact resolve eq75751 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75751
  have eq75952 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75923
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq75923
    | exact resolve eq75923 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq75923
  have eq75962 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq527 eq75952
    | exact resolve eq75952 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq75952
  have eq196069 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq507
       grind)
    | exact superpose eq507 eq86
    | exact resolve eq86 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq507
  have eq196081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq196069 eq75962
    | exact resolve eq75962 eq196069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75962 eq196069
  have eq196100 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq196081
       have r₂ := eq28
       grind)
    | exact resolve eq196081 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196081
  have eq196243 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq196100 eq12517
    | exact resolve eq12517 eq196100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196100
  have eq196396 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq5349 eq196243
    | exact resolve eq196243 eq5349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349 eq196243
  have eq196397 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq196396
  have eq196696 : ∀ X0 X1 : G, y = (M.op (M.op X0 y) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12517 y y X1 X0
       have i₂ := eq196397
       grind)
    | exact superpose eq196397 eq12517
    | exact resolve eq12517 eq196397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12517 eq196397
  have eq196849 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4410 eq196696
    | exact resolve eq196696 eq4410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410 eq196696
  have eq196850 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq196849
  have eq197221 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq196850 eq30
    | exact resolve eq30 eq196850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq196850
  have eq197430 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq197221
    | exact resolve eq197221 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq197221
  have eq197431 : x = y := by grind
  clear eq197430
  have eq197453 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq197431
       grind)
    | exact superpose eq197431 eq19
    | exact resolve eq19 eq197431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq197454 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq197431
       grind)
    | exact superpose eq197431 eq25
    | exact resolve eq25 eq197431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq197431
  have eq197659 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq197454
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq197454
    | exact resolve eq197454 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq197454
  have eq197696 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq197659 eq27
    | exact resolve eq27 eq197659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq197659
  have eq201604 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq197696 eq69
    | exact resolve eq69 eq197696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq197696
  have eq201965 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq201604
       have i₂ := eq197453
       grind)
    | exact superpose eq197453 eq201604
    | exact resolve eq201604 eq197453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197453 eq201604
  have eq202102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq201965 eq15
    | exact resolve eq15 eq201965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201965
  have eq202178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq202102
    | exact resolve eq202102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq202102
  have eq202199 : False := by grind
  exact eq202199

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pyx_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq212 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op sF0 (M.op x X0)) x)
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq217 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op sF4 (M.op x X0)) x)
       have i₂ := eq14 X0 sF4 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq481 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X1 (M.op X1 X0) x
       have i₂ := eq56 X1 X1 X0 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq678 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2) X3 X1
       have i₂ := eq56 X3 X1 X0 X2
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq1531 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq676 (M.op X1 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq676 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq676 eq481
    | exact resolve eq481 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1636 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq676 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq491 X2 X0 X1
       have i₂ := eq676 X0 (M.op X1 X2)
       grind)
    | exact superpose eq676 eq491
    | exact resolve eq491 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1915 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq676 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq676 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq676 eq673
    | exact resolve eq673 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq2164 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1915 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1531 X2 X1 X0
       grind)
    | exact superpose eq1531 eq1915
    | exact resolve eq1915 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531 eq1915
  have eq2283 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq676 (M.op sF0 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq212 X0 X0
       have i₂ := eq676 X0 (M.op sF0 (M.op X0 X0))
       grind)
    | exact superpose eq676 eq212
    | exact resolve eq212 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2310 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq676 (M.op sF4 (M.op X1 X0)) X1
       grind)
    | (have i₁ := eq217 X0 X0
       have i₂ := eq676 X0 (M.op sF4 (M.op X0 X0))
       grind)
    | exact superpose eq676 eq217
    | exact resolve eq217 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq676
  have eq12356 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3))) (M.op X3 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq678 X0 X1 X2 X3
       have i₂ := eq491 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq678 X0 X1 X2 X3
       have i₂ := eq491 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq491 eq678
    | exact resolve eq678 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq678
  have eq12357 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op (M.op X1 X0) (M.op X2 X3)) X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12356 X0 X1 X2 X3
       have i₂ := eq1636 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3)) X2
       grind)
    | exact superpose eq1636 eq12356
    | exact resolve eq12356 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636 eq12356
  have eq12358 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 (M.op (M.op X1 X0) (M.op X2 X3)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12357 X0 X1 X2 X3
       have i₂ := eq2164 X2 (M.op X3 X0) (M.op (M.op X1 X0) (M.op X2 X3))
       grind)
    | (have i₁ := eq12357 X0 X1 X2 X3
       have i₂ := eq2164 (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X3 X0) X2
       grind)
    | exact superpose eq2164 eq12357
    | exact resolve eq12357 eq2164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164 eq12357
  have eq31847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq31848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq31847
    | exact resolve eq31847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31847
  have eq31859 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq31848
       have r₂ := eq28
       grind)
    | exact resolve eq31848 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31848
  have eq31863 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq31859
    | exact resolve eq31859 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31859
  have eq31924 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq31863 eq12358
    | exact resolve eq12358 eq31863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31863
  have eq31957 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq2310 eq31924
    | exact resolve eq31924 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310 eq31924
  have eq31958 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31957
  have eq32064 : ∀ X0 X1 : G, x = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) (M.op X1 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12358 x x X1 X0
       have i₂ := eq31958
       grind)
    | exact superpose eq31958 eq12358
    | exact resolve eq12358 eq31958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12358 eq31958
  have eq32097 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2283 eq32064
    | exact resolve eq32064 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283 eq32064
  have eq32098 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq32097
  have eq32160 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq32098 eq30
    | exact resolve eq30 eq32098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32098
  have eq32296 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq32160
    | exact resolve eq32160 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32160
  have eq32297 : x = y := by grind
  clear eq32296
  have eq32317 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32297
       grind)
    | exact superpose eq32297 eq19
    | exact resolve eq19 eq32297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32318 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32297
       grind)
    | exact superpose eq32297 eq25
    | exact resolve eq25 eq32297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32297
  have eq32455 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32318
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32318
    | exact resolve eq32318 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32318
  have eq32474 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32455 eq27
    | exact resolve eq27 eq32455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32455
  have eq32820 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32474 eq69
    | exact resolve eq69 eq32474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq32474
  have eq32947 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32820
       have i₂ := eq32317
       grind)
    | exact superpose eq32317 eq32820
    | exact resolve eq32820 eq32317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32317 eq32820
  have eq32982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32947 eq15
    | exact resolve eq15 eq32947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32947
  have eq33024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq32982
    | exact resolve eq32982 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq32982
  have eq33033 : False := by grind
  exact eq33033

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq31 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq31 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq31 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq40 X1 (σ X0)
       grind)
    | exact superpose eq40 eq28
    | exact resolve eq28 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq40
  have eq72 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64
    | exact resolve eq64 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq153 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq15
    | (have j1 := eq51 (σ X0)
       grind)
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq76 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq322 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq323 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq322 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq326 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq323
    | (have j0 := eq323 X0 X1
       grind)
    | exact resolve eq323 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq331 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq326 X0 X1
       have j1 := eq319 X0 X1
       grind)
    | (have r₁ := eq326 X0 X1
       have r₂ := eq319 X0 X1
       grind)
    | (have r₁ := eq326 X0 X0
       have r₂ := eq319 X0 X0
       grind)
    | exact resolve eq326 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq326
  have eq1360 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq153 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq1641 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq331 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq331
    | exact resolve eq331 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1653 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq331 x y
       grind)
    | exact superpose eq331 eq16
    | (have j1 := eq331 x x
       grind)
    | exact resolve eq16 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq1687 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1641 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1641
    | (have j0 := eq1641 X0 X1
       grind)
    | exact resolve eq1641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1641
  have eq1688 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1687 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1687
    | (have j0 := eq1687 X1 X1
       grind)
    | exact resolve eq1687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq1828 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1688 (τ X1) X0
       grind)
    | exact superpose eq1688 eq17
    | (have j1 := eq1688 X0 X0
       grind)
    | exact resolve eq17 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1688
  have eq2035 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1828 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1828
    | (have j0 := eq1828 X1 X1
       grind)
    | exact resolve eq1828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq2092 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2035 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2035
    | (have j0 := eq2035 X0 X1
       grind)
    | exact resolve eq2035 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2794 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1653
       have i₂ := eq2092 y x
       grind)
    | exact superpose eq2092 eq1653
    | (have j1 := eq2092 x (σ x)
       grind)
    | (have r₁ := eq1653
       have r₂ := eq2092 y x
       grind)
    | exact resolve eq1653 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653 eq2092
  have eq2795 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2794
  have eq2849 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq2795
       grind)
    | exact superpose eq2795 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq2795
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq2795
       grind)
    | exact resolve eq12 eq2795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795
  have eq2882 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq2849 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849
  have eq2890 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1360 x
       have i₂ := eq2882 x
       grind)
    | exact superpose eq2882 eq1360
    | (have j0 := eq1360 x
       grind)
    | exact resolve eq1360 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360 eq2882
  have eq2910 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2890
  have eq2911 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2910
  have eq2976 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 (σ x) X0
       have i₂ := eq2911
       grind)
    | exact superpose eq2911 eq31
    | exact resolve eq31 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2980 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 X0 (σ x)
       have i₂ := eq2911
       grind)
    | exact superpose eq2911 eq72
    | exact resolve eq72 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3022 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2980 X0
       have i₂ := eq2911
       grind)
    | exact superpose eq2911 eq2980
    | exact resolve eq2980 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq3026 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2976 X0
       have i₂ := eq2911
       grind)
    | exact superpose eq2911 eq2976
    | exact resolve eq2976 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911 eq2976
  have eq3035 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq3022 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3022
    | exact resolve eq3022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq3044 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq3035 x
       grind)
    | exact superpose eq3035 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq3035
  have eq3060 : x = (M.op x x) := by grind
  clear eq3044
  have eq3200 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 x X0
       have i₂ := eq3060
       grind)
    | exact superpose eq3060 eq31
    | exact resolve eq31 eq3060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq3252 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3200 X0
       have i₂ := eq3060
       grind)
    | exact superpose eq3060 eq3200
    | exact resolve eq3200 eq3060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060 eq3200
  have eq3455 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3026 (σ y)
       grind)
    | exact superpose eq3026 eq16
    | exact resolve eq16 eq3026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3544 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3455
       have i₂ := eq3252 y
       grind)
    | exact superpose eq3252 eq3455
    | exact resolve eq3455 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252 eq3455
  have eq3545 : False := by grind
  exact eq3545
