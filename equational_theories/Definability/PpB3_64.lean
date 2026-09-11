import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxy_x_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq91 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq95
    | exact resolve eq95 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq95
  have eq248 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq16
    | (have r₁ := eq16
       have r₂ := eq106 x y
       grind)
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq256 : False := by grind
  exact eq256

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pyx_pyy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq64 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq92 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq64 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq93 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq93 (σ X0) (σ X1)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq96
    | exact resolve eq96 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq96
  have eq249 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107 x y
       grind)
    | exact superpose eq107 eq16
    | (have r₁ := eq16
       have r₂ := eq107 x y
       grind)
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq257 : False := by grind
  exact eq257

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_x_pyy_pxy_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq40 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | (have r₁ := eq52 X0 X0
       have r₂ := eq40 X0
       grind)
    | exact resolve eq52 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq80 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq34
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq113 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq132 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq132
    | (have j0 := eq132 X0 X1
       grind)
    | exact resolve eq132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq477 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq147
    | exact resolve eq147 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq604 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq638 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq604 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq604
    | (have j0 := eq604 X0 X1
       grind)
    | exact resolve eq604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq4129 : (σ (M.op x y)) ≠ (σ x) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113 x (σ y)
       grind)
    | exact superpose eq113 eq16
    | (have j1 := eq113 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq113 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4136 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) X1
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq58
    | (have j0 := eq58 (σ X0) X1
       have j1 := eq113 X0 X1
       grind)
    | (have r₁ := eq58 (σ X0) X1
       have r₂ := eq113 X0 X1
       grind)
    | (have r₁ := eq58 (σ X0) X1
       have r₂ := eq113 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq58 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq113
  have eq4151 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4152 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4151
  have eq4161 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4129
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4129
    | exact resolve eq4129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129
  have eq4167 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4152 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4152
    | exact resolve eq4152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4212 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) X0
       have i₂ := eq4152 X1 (σ X0)
       grind)
    | exact superpose eq4152 eq26
    | (have j1 := eq4152 X0 (σ X1)
       grind)
    | exact resolve eq26 eq4152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4152
  have eq4274 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4212 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4212
    | (have j0 := eq4212 X0 X1
       grind)
    | exact resolve eq4212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4212
  have eq4285 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4167 X0 X1
       have i₂ := eq80 X1 X0
       grind)
    | exact superpose eq80 eq4167
    | (have j0 := eq4167 X0 X1
       grind)
    | exact resolve eq4167 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4167
  have eq4308 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4274 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4274
    | (have j0 := eq4274 X0 X1
       grind)
    | exact resolve eq4274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq4315 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4308 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4308
    | (have j0 := eq4308 X0 X1
       grind)
    | exact resolve eq4308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4308
  have eq4344 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4285 X0 X1
       grind)
    | exact superpose eq4285 eq11
    | (have j1 := eq4285 X0 X1
       grind)
    | exact resolve eq11 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285
  have eq4452 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4344 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4344
    | (have j0 := eq4344 X0 X1
       grind)
    | exact resolve eq4344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344
  have eq4585 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4452 (τ X0) X1
       grind)
    | exact superpose eq4452 eq18
    | (have j1 := eq4452 (τ X0) X1
       grind)
    | exact resolve eq18 eq4452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4452
  have eq5187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4315 X1 X0
       grind)
    | exact superpose eq4315 eq11
    | (have j1 := eq4315 X1 X0
       grind)
    | exact resolve eq11 eq4315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq6107 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5187 x y
       grind)
    | exact superpose eq5187 eq16
    | (have j1 := eq5187 x y
       grind)
    | exact resolve eq16 eq5187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5187
  have eq6172 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6107
       have i₂ := eq477 y x
       grind)
    | exact superpose eq477 eq6107
    | (have j1 := eq477 y x
       grind)
    | (have r₁ := eq6107
       have r₂ := eq477 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6107
       have r₂ := eq477 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6107 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq6107
  have eq6177 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq6172
  have eq6287 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6177
       grind)
    | exact superpose eq6177 eq16
    | exact resolve eq16 eq6177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6177
  have eq6288 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6287
       have i₂ := eq40 (σ x)
       grind)
    | exact superpose eq40 eq6287
    | exact resolve eq6287 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6287
  have eq6289 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6288
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq6288
    | exact resolve eq6288 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6288
  have eq6290 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6289
  have eq6294 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43 x y
       have i₂ := eq6290
       grind)
    | exact superpose eq6290 eq43
    | exact resolve eq43 eq6290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6304 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  have eq6316 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6294
       have i₂ := eq6290
       grind)
    | exact superpose eq6290 eq6294
    | exact resolve eq6294 eq6290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6290 eq6294
  have eq6334 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6316
  have eq6338 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6334
       have r₂ := eq6304
       grind)
    | exact resolve eq6334 eq6304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6304 eq6334
  have eq7442 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4585 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4585
    | exact resolve eq4585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4585
  have eq7556 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7442 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7442
    | (have j0 := eq7442 X0 X1
       grind)
    | exact resolve eq7442 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7442
  have eq34889 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4161
       have i₂ := eq6338
       grind)
    | exact superpose eq6338 eq4161
    | exact resolve eq4161 eq6338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4161 eq6338
  have eq34895 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq34889
  have eq34896 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq34895
  have eq35152 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq34896
       grind)
    | exact superpose eq34896 eq10
    | exact resolve eq10 eq34896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34896
  have eq35260 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq35152
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35152
    | exact resolve eq35152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35152
  have eq35262 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35260
       grind)
    | exact superpose eq35260 eq16
    | exact resolve eq16 eq35260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35260
  have eq35263 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq35262
       have i₂ := eq40 (σ x)
       grind)
    | exact superpose eq40 eq35262
    | exact resolve eq35262 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35262
  have eq35264 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq35263
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq35263
    | exact resolve eq35263 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35263
  have eq35265 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq35264
  have eq35705 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq35265
       grind)
    | exact superpose eq35265 eq11
    | exact resolve eq11 eq35265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35265
  have eq35838 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35705
       grind)
    | exact superpose eq35705 eq16
    | exact resolve eq16 eq35705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35864 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq43 (σ x) (σ y)
       have i₂ := eq35705
       grind)
    | exact superpose eq35705 eq43
    | exact resolve eq43 eq35705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq36285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq35838
       have i₂ := eq7556 x y
       grind)
    | exact superpose eq7556 eq35838
    | (have j1 := eq7556 x y
       grind)
    | (have r₁ := eq35838
       have r₂ := eq7556 x y
       grind)
    | (have r₁ := eq35838
       have r₂ := eq7556 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq35838
       have r₂ := eq7556 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq35838 eq7556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7556
  have eq36286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq35838
       have i₂ := eq638 y x
       grind)
    | exact superpose eq638 eq35838
    | (have j1 := eq638 y x
       grind)
    | (have r₁ := eq35838
       have r₂ := eq638 y x
       grind)
    | (have r₁ := eq35838
       have r₂ := eq638 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq35838
       have r₂ := eq638 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq35838 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq36287 : x = y ∨ x = (M.op x y) := by grind
  clear eq36286
  have eq36288 : x = y ∨ y = (k x y) := by grind
  clear eq36285
  have eq36297 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35838
       have i₂ := eq36287
       grind)
    | exact superpose eq36287 eq35838
    | exact resolve eq35838 eq36287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36287
  have eq36298 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq36297
  have eq36302 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36298
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq36298
    | exact resolve eq36298 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36298
  have eq36303 : x = (M.op x y) := by grind
  clear eq36302
  have eq36897 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq35838
       have i₂ := eq36288
       grind)
    | exact superpose eq36288 eq35838
    | exact resolve eq35838 eq36288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36288
  have eq36901 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by grind
  clear eq36897
  have eq36905 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq36901
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq36901
    | exact resolve eq36901 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq36901
  have eq36906 : y = (k x y) := by grind
  clear eq36905
  have eq36927 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq35838
       have i₂ := eq36906
       grind)
    | exact superpose eq36906 eq35838
    | exact resolve eq35838 eq36906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35838
  have eq36968 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq36927
       have i₂ := eq36303
       grind)
    | exact superpose eq36303 eq36927
    | exact resolve eq36927 eq36303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36303 eq36927
  have eq37927 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq35864
       have i₂ := eq96 x (k x y)
       grind)
    | exact superpose eq96 eq35864
    | (have j1 := eq96 x (k x y)
       grind)
    | exact resolve eq35864 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq35864
  have eq37992 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq37927
       have i₂ := eq36906
       grind)
    | exact superpose eq36906 eq37927
    | exact resolve eq37927 eq36906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37927
  have eq37993 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq37992
  have eq38010 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq37993
       have i₂ := eq36906
       grind)
    | exact superpose eq36906 eq37993
    | exact resolve eq37993 eq36906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37993
  have eq38024 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq38010
       have i₂ := eq35705
       grind)
    | exact superpose eq35705 eq38010
    | exact resolve eq38010 eq35705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35705 eq38010
  have eq38025 : (σ x) = (σ (k x y)) := by grind
  clear eq38024
  have eq38032 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq38025
       have i₂ := eq36906
       grind)
    | exact superpose eq36906 eq38025
    | exact resolve eq38025 eq36906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36906 eq38025
  have eq38039 : False := by grind
  exact eq38039

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pxy_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq120 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq110 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq9
    | exact resolve eq9 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
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
  have eq509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq536 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq110 (σ X1)
       grind)
    | exact superpose eq110 eq509
    | (have j0 := eq509 X0 X1
       grind)
    | exact resolve eq509 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq539 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq506 X0 X1
       have i₂ := eq110 X1
       grind)
    | exact superpose eq110 eq506
    | (have j0 := eq506 X0 X1
       grind)
    | exact resolve eq506 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq803 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq539 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq539
    | exact resolve eq539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq845 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq803 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq803
    | (have j0 := eq803 X0 X1
       grind)
    | exact resolve eq803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq911 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq536 x y
       grind)
    | exact superpose eq536 eq16
    | (have j1 := eq536 x y
       grind)
    | exact resolve eq16 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq5590 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq911
       have i₂ := eq845 x y
       grind)
    | exact superpose eq845 eq911
    | (have j1 := eq845 (σ x) (σ y)
       grind)
    | (have r₁ := eq911
       have r₂ := eq845 x y
       grind)
    | (have r₁ := eq911
       have r₂ := eq845 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq911
       have r₂ := eq845 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq911 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845 eq911
  have eq5591 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5590
  have eq5595 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5591
       grind)
    | exact superpose eq5591 eq16
    | exact resolve eq16 eq5591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5591
  have eq5596 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5595
       have r₂ := eq22 x
       grind)
    | exact resolve eq5595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5595
  have eq5599 : (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120 x y
       have i₂ := eq5596
       grind)
    | exact superpose eq5596 eq120
    | exact resolve eq120 eq5596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5615 : y = (τ (σ x)) ∨ x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5599
       grind)
    | exact superpose eq5599 eq10
    | exact resolve eq10 eq5599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5599
  have eq5660 : x = y ∨ x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5615
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5615
    | exact resolve eq5615 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5615
  have eq5667 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5660
       grind)
    | exact superpose eq5660 eq16
    | exact resolve eq16 eq5660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5660
  have eq5668 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have r₁ := eq5667
       have r₂ := eq22 x
       grind)
    | exact resolve eq5667 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5673 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5668
       grind)
    | exact superpose eq5668 eq16
    | exact resolve eq16 eq5668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq5701 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5673
       have i₂ := eq5596
       grind)
    | exact superpose eq5596 eq5673
    | exact resolve eq5673 eq5596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5673
  have eq5712 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5701
  have eq5866 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5596
       have i₂ := eq5712
       grind)
    | exact superpose eq5712 eq5596
    | exact resolve eq5596 eq5712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596 eq5712
  have eq5888 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5866
  have eq5898 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5888
       grind)
    | exact superpose eq5888 eq16
    | exact resolve eq16 eq5888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888
  have eq5908 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5898
       have r₂ := eq22 x
       grind)
    | exact resolve eq5898 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq5912 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5908
       grind)
    | exact superpose eq5908 eq10
    | exact resolve eq10 eq5908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5908
  have eq5957 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5912
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5912
    | exact resolve eq5912 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5912
  have eq5964 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5957
       grind)
    | exact superpose eq5957 eq16
    | exact resolve eq16 eq5957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5957
  have eq5974 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5964
       have r₂ := eq22 x
       grind)
    | exact resolve eq5964 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5964
  have eq5984 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5974
       grind)
    | exact superpose eq5974 eq16
    | exact resolve eq16 eq5974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5987 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq120 (σ x) (σ y)
       have i₂ := eq5974
       grind)
    | exact superpose eq5974 eq120
    | exact resolve eq120 eq5974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq6004 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5987
       have i₂ := eq5974
       grind)
    | exact superpose eq5974 eq5987
    | exact resolve eq5987 eq5974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5987
  have eq6053 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5974
       have i₂ := eq6004
       grind)
    | exact superpose eq6004 eq5974
    | exact resolve eq5974 eq6004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5974 eq6004
  have eq6112 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6053
       grind)
    | exact superpose eq6053 eq10
    | exact resolve eq10 eq6053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6053
  have eq6157 : x = y := by
    first
    | (have i₁ := eq6112
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6112
    | exact resolve eq6112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6112
  have eq6323 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5984
       have i₂ := eq6157
       grind)
    | exact superpose eq6157 eq5984
    | exact resolve eq5984 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5984 eq6157
  have eq6325 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6323
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq6323
    | exact resolve eq6323 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq6323
  have eq6326 : False := by grind
  exact eq6326

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq175 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq177 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq181 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq182 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq185 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | exact resolve eq175 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq186 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq195 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq212 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq195
    | (have j0 := eq195 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq398 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq16
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq398
       have i₂ := eq212 y x
       grind)
    | exact superpose eq212 eq398
    | (have j1 := eq212 (σ x) (σ y)
       grind)
    | (have r₁ := eq398
       have r₂ := eq212 y x
       grind)
    | (have r₁ := eq398
       have r₂ := eq212 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq398
       have r₂ := eq212 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq398 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq398
  have eq421 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq420
  have eq424 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq421
       grind)
    | exact superpose eq421 eq16
    | exact resolve eq16 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq425 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq424
       have r₂ := eq23 x
       grind)
    | exact resolve eq424 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq424
  have eq426 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq425
       grind)
    | exact superpose eq425 eq16
    | exact resolve eq16 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq425
       grind)
    | exact superpose eq425 eq10
    | exact resolve eq10 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq442 : x = y := by
    first
    | (have i₁ := eq427
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq427
    | exact resolve eq427 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq443 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq426
       have i₂ := eq111 (σ x)
       grind)
    | exact superpose eq111 eq426
    | exact resolve eq426 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq445 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq443
       have i₂ := eq442
       grind)
    | exact superpose eq442 eq443
    | exact resolve eq443 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq443
  have eq446 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq445
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq445
    | exact resolve eq445 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq445
  have eq447 : False := by grind
  exact eq447

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq144 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq136 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq136
    | (have j0 := eq136 X0
       grind)
    | exact resolve eq136 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq136
  have eq145 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq144 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144
    | (have j0 := eq144 X0
       grind)
    | exact resolve eq144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq146 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq145 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq145 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq145 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq149 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq146 (σ X0)
       grind)
    | exact superpose eq146 eq15
    | exact resolve eq15 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq149 X0
       have i₂ := eq146 X0
       grind)
    | exact superpose eq146 eq149
    | exact resolve eq149 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq149
  have eq238 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87 x y
       grind)
    | exact superpose eq87 eq16
    | (have j1 := eq87 x y
       grind)
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1075 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1115 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1075 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1075
    | (have j0 := eq1075 X0 X1
       grind)
    | exact resolve eq1075 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1195 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq244 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq244
    | (have j0 := eq244 (τ X0) (τ X1)
       grind)
    | exact resolve eq244 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1213 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1195 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1195
    | (have j0 := eq1195 X0 X1
       grind)
    | exact resolve eq1195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1219 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1213 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1213
    | (have j0 := eq1213 X0 X1
       grind)
    | exact resolve eq1213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1223 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1219 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1219
    | (have j0 := eq1219 X0 X1
       grind)
    | exact resolve eq1219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1224 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1223 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1223
    | (have j0 := eq1223 X0 X1
       grind)
    | exact resolve eq1223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1225 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1224 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1224
    | (have j0 := eq1224 X0 X1
       grind)
    | exact resolve eq1224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1226 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1225 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1225
    | (have j0 := eq1225 X0 X1
       grind)
    | exact resolve eq1225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1465 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq238
       have i₂ := eq1115 y x
       grind)
    | exact superpose eq1115 eq238
    | (have j1 := eq1115 (σ x) (σ y)
       grind)
    | (have r₁ := eq238
       have r₂ := eq1115 y x
       grind)
    | (have r₁ := eq238
       have r₂ := eq1115 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq238
       have r₂ := eq1115 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq238 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq1115
  have eq1466 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1465
  have eq11285 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq16
    | exact resolve eq16 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq11286 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11285
       have r₂ := eq160 x
       grind)
    | exact resolve eq11285 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11285
  have eq11374 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq11286
       grind)
    | exact superpose eq11286 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq11286
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11286
       grind)
    | exact resolve eq12 eq11286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11286
  have eq11391 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11374
  have eq11395 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq244 x y
       have i₂ := eq11391
       grind)
    | exact superpose eq11391 eq244
    | (have j0 := eq244 x y
       grind)
    | exact resolve eq244 eq11391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq11391
  have eq11409 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11395
  have eq11410 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11409
  have eq11554 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11410
       grind)
    | exact superpose eq11410 eq16
    | exact resolve eq16 eq11410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11557 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq11410
       grind)
    | exact superpose eq11410 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11410
       grind)
    | exact resolve eq12 eq11410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11410
  have eq11574 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11557
  have eq11592 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq11574
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq11574
    | exact resolve eq11574 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11574
  have eq11758 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11592
       grind)
    | exact superpose eq11592 eq10
    | exact resolve eq10 eq11592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11592
  have eq11843 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq11758
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11758
    | exact resolve eq11758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11758
  have eq11851 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11843
       grind)
    | exact superpose eq11843 eq16
    | exact resolve eq16 eq11843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11843
  have eq11852 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq11851
       have r₂ := eq160 x
       grind)
    | exact resolve eq11851 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11851
  have eq11937 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq11852
       grind)
    | exact superpose eq11852 eq10
    | exact resolve eq10 eq11852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11852
  have eq12023 : x = (k x y) := by
    first
    | (have i₁ := eq11937
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11937
    | exact resolve eq11937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11937
  have eq12036 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1226 x y
       have i₂ := eq12023
       grind)
    | exact superpose eq12023 eq1226
    | (have j0 := eq1226 x y
       grind)
    | (have r₁ := eq1226 x y
       have r₂ := eq12023
       grind)
    | exact resolve eq1226 eq12023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq12023
  have eq12047 : x = y ∨ x = (M.op x y) := by grind
  clear eq12036
  have eq12128 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12047
       grind)
    | exact superpose eq12047 eq16
    | exact resolve eq16 eq12047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12047
  have eq12133 : x = (M.op x y) := by
    first
    | (have r₁ := eq12128
       have r₂ := eq160 x
       grind)
    | exact resolve eq12128 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12128
  have eq12137 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11554
       have i₂ := eq12133
       grind)
    | exact superpose eq12133 eq11554
    | exact resolve eq11554 eq12133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11554 eq12133
  have eq12157 : (σ x) = (σ y) := by grind
  clear eq12137
  have eq12236 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12157
       grind)
    | exact superpose eq12157 eq10
    | exact resolve eq10 eq12157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12157
  have eq12321 : x = y := by
    first
    | (have i₁ := eq12236
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12236
    | exact resolve eq12236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12236
  have eq12329 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12321
       grind)
    | exact superpose eq12321 eq16
    | exact resolve eq16 eq12321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12321
  have eq12335 : False := by grind
  exact eq12335

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq435 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq439 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq448 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq447 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq456 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq448 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq448 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq448 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq460 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq435
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq435 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq465 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq460
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq460
    | exact resolve eq460 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq479 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq456 X0 (τ X1)
       grind)
    | exact superpose eq456 eq18
    | (have j1 := eq456 X0 (τ X1)
       grind)
    | exact resolve eq18 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq496 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq863 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq479 (τ X0) X1
       grind)
    | exact superpose eq479 eq17
    | (have j1 := eq479 (τ X0) X1
       grind)
    | exact resolve eq17 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq479
  have eq868 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq863 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq863
    | (have j0 := eq863 X0 X1
       grind)
    | exact resolve eq863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq882 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq868 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq868
    | (have j0 := eq868 X0 X1
       grind)
    | exact resolve eq868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq885 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq882 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq882
    | (have j0 := eq882 X0 X1
       grind)
    | exact resolve eq882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq948 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq885 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq885
    | (have j0 := eq885 X1 (σ X0)
       grind)
    | exact resolve eq885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1332 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq948 X0 X0
       have i₂ := eq456 X0 (σ X0)
       grind)
    | exact superpose eq456 eq948
    | (have j0 := eq948 X1 X0
       have j1 := eq456 X0 (σ X1)
       grind)
    | exact resolve eq948 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq948
  have eq1368 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1332 X0 X1
       have j1 := eq496 X0 (σ X1)
       grind)
    | (have r₁ := eq1332 X0 X1
       have r₂ := eq496 X0 (σ X1)
       grind)
    | exact resolve eq1332 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq1332
  have eq1541 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1368 (σ X0) X1
       grind)
    | exact superpose eq1368 eq28
    | (have j1 := eq1368 (σ X0) X1
       grind)
    | exact resolve eq28 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1368
  have eq1552 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1541 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1541
    | (have j0 := eq1541 X0 X1
       grind)
    | exact resolve eq1541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1566 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1552 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1552
    | (have j0 := eq1552 X0 X1
       grind)
    | exact resolve eq1552 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1575 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1566 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1566
    | (have j0 := eq1566 X0 X1
       grind)
    | exact resolve eq1566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1667 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1575 x y
       grind)
    | exact superpose eq1575 eq16
    | (have j1 := eq1575 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1575 x y
       grind)
    | exact resolve eq16 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575
  have eq1691 : x = (k x y) := by grind
  clear eq1667
  have eq1917 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq465
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq465
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq465 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1918 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1917
  have eq1919 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1918
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1918 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq1920 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1919
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq1919
    | exact resolve eq1919 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq1921 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1920
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq1920
    | exact resolve eq1920 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq1922 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq465
       have i₂ := eq1921
       grind)
    | exact superpose eq1921 eq465
    | exact resolve eq465 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465 eq1921
  have eq1932 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1922
  have eq1933 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1932
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq1932
    | exact resolve eq1932 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq1934 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1933
  have eq1936 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1934
       grind)
    | exact superpose eq1934 eq16
    | exact resolve eq16 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq1965 : (σ x) ≠ (σ x) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1936
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1936
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1936 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1966 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1965
  have eq1968 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1966
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1966 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq1969 : x = (M.op x y) := by
    first
    | (have i₁ := eq1968
       have i₂ := eq1691
       grind)
    | exact superpose eq1691 eq1968
    | exact resolve eq1968 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691 eq1968
  have eq1970 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1936
       have i₂ := eq1969
       grind)
    | exact superpose eq1969 eq1936
    | exact resolve eq1936 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936 eq1969
  have eq1982 : False := by grind
  exact eq1982

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq452 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq472 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq452
    | (have j0 := eq452 X0 X1
       grind)
    | exact resolve eq452 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq478 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq472 X0 X1
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq472 X1 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq472 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq598 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq478
    | exact resolve eq478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq478 (σ X1) X0
       grind)
    | exact superpose eq478 eq15
    | (have j1 := eq478 (σ X1) X0
       grind)
    | exact resolve eq15 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq664 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq598 X0 (τ X1)
       grind)
    | exact superpose eq598 eq17
    | (have j1 := eq598 X0 (τ X1)
       grind)
    | exact resolve eq17 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq598
  have eq1706 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq664 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq664
    | exact resolve eq664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq1771 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1706 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1706
    | (have j0 := eq1706 X0 X1
       grind)
    | exact resolve eq1706 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq3439 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq614 x y
       grind)
    | exact superpose eq614 eq16
    | (have j1 := eq614 x y
       grind)
    | exact resolve eq16 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3496 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq614 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq4133 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3439
       have i₂ := eq1771 y x
       grind)
    | exact superpose eq1771 eq3439
    | (have j1 := eq1771 (σ y) (σ x)
       grind)
    | (have r₁ := eq3439
       have r₂ := eq1771 y x
       grind)
    | exact resolve eq3439 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq4134 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4133
  have eq4138 : x ≠ (M.op x x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4134
       grind)
    | exact superpose eq4134 eq12
    | exact resolve eq12 eq4134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4139 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq4134
       grind)
    | exact superpose eq4134 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4134
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4134
       grind)
    | exact resolve eq13 eq4134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4134
  have eq4157 : x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4139
  have eq4158 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4138
       have r₂ := eq4157
       grind)
    | exact resolve eq4138 eq4157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4138 eq4157
  have eq4317 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3496 x y
       have i₂ := eq4158
       grind)
    | exact superpose eq4158 eq3496
    | (have j0 := eq3496 x y
       grind)
    | exact resolve eq3496 eq4158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496 eq4158
  have eq4322 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4317
  have eq4323 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4322
  have eq4339 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4323
       grind)
    | exact superpose eq4323 eq16
    | exact resolve eq16 eq4323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4340 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq81 x (σ y)
       have i₂ := eq4323
       grind)
    | exact superpose eq4323 eq81
    | exact resolve eq81 eq4323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq4346 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4323
       grind)
    | exact superpose eq4323 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4323
       grind)
    | exact resolve eq13 eq4323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4323
  have eq4364 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4346
  have eq4382 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4364
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4364
    | exact resolve eq4364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364
  have eq4388 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4340
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4340
    | exact resolve eq4340 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4340
  have eq4403 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq4382
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq4382
    | exact resolve eq4382 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4382
  have eq4406 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq4403
       have r₂ := eq4388
       grind)
    | exact resolve eq4403 eq4388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4388 eq4403
  have eq4545 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1771 y x
       have i₂ := eq4406
       grind)
    | exact superpose eq4406 eq1771
    | (have j0 := eq1771 y x
       grind)
    | exact resolve eq1771 eq4406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771 eq4406
  have eq4615 : x = (M.op x y) := by
    first
    | (have r₁ := eq4545
       have r₂ := eq4339
       grind)
    | exact resolve eq4545 eq4339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545
  have eq4760 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4339
       have i₂ := eq4615
       grind)
    | exact superpose eq4615 eq4339
    | exact resolve eq4339 eq4615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4339 eq4615
  have eq4784 : False := by grind
  exact eq4784
