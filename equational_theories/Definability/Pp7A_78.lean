import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_y_pyy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq91 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
  have eq92 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
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

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxx_x_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
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
  have eq91 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
  have eq92 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
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

`x □ y = if X = Y then X else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_x_pyy_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq77 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq109 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq111 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq115 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq77 (τ X1)
       grind)
    | exact superpose eq77 eq111
    | (have j0 := eq111 X0 X1
       grind)
    | exact resolve eq111 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq116 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq77 (σ X1)
       grind)
    | exact superpose eq77 eq109
    | (have j0 := eq109 X0 X1
       grind)
    | exact resolve eq109 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq120 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq144 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq129
    | (have j0 := eq129 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq282 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq16
    | (have j1 := eq120 x y
       grind)
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq296 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq282
       have i₂ := eq144 y x
       grind)
    | exact superpose eq144 eq282
    | (have j1 := eq144 (σ x) (σ y)
       grind)
    | (have r₁ := eq282
       have r₂ := eq144 y x
       grind)
    | (have r₁ := eq282
       have r₂ := eq144 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq282
       have r₂ := eq144 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq282 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq282
  have eq297 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq296
  have eq300 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq297
       grind)
    | exact superpose eq297 eq16
    | exact resolve eq16 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq301 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq300
       have i₂ := eq77 (σ x)
       grind)
    | exact superpose eq77 eq300
    | exact resolve eq300 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq302 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq301
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq301
    | exact resolve eq301 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq303 : (σ x) = (σ y) := by grind
  clear eq302
  have eq304 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq303
       grind)
    | exact superpose eq303 eq16
    | exact resolve eq16 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq303
       grind)
    | exact superpose eq303 eq10
    | exact resolve eq10 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq318 : x = y := by
    first
    | (have i₁ := eq305
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq305
    | exact resolve eq305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq319 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq304
       have i₂ := eq77 (σ x)
       grind)
    | exact superpose eq77 eq304
    | exact resolve eq304 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq320 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq319
       have i₂ := eq318
       grind)
    | exact superpose eq318 eq319
    | exact resolve eq319 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq319
  have eq321 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq320
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq320
    | exact resolve eq320 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq320
  have eq322 : False := by grind
  exact eq322

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then Y else if m(X,Y) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_y_x_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq76 : ∀ X0 : G, (M.op X0 X0) = X0 := by
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
  have eq79 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq76 (M.op X0 X1)
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq79 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq79
    | (have j1 := eq14 (M.op X1 (M.op X1 (M.op X0 X0))) X1
       grind)
    | exact resolve eq79 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq354 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq76 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq345
    | (have j0 := eq345 X0 X1
       grind)
    | exact resolve eq345 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq480 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq354 X1 X0
       grind)
    | exact superpose eq354 eq359
    | (have j0 := eq359 X0 X1
       have j1 := eq354 (M.op X1 X0) X1
       grind)
    | exact resolve eq359 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq495 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq508 : ∀ X0 X1 : G, X0 = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0 X1
       have i₂ := eq495 X1 X0
       grind)
    | exact superpose eq495 eq354
    | (have j0 := eq354 X0 X1
       have j1 := eq495 X0 X1
       grind)
    | exact resolve eq354 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq495
  have eq517 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq508 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq534 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq517 X1 (τ X0)
       grind)
    | exact superpose eq517 eq19
    | (have j1 := eq517 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq537 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq517 (σ X1) (σ X0)
       grind)
    | exact superpose eq517 eq15
    | (have j1 := eq517 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq635 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq534 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq534
    | exact resolve eq534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq682 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq635 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq635
    | (have j0 := eq635 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq635 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq818 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq537 x y
       grind)
    | exact superpose eq537 eq16
    | (have j1 := eq537 x y
       grind)
    | exact resolve eq16 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq855 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq818
       have i₂ := eq682 x y
       grind)
    | exact superpose eq682 eq818
    | (have j1 := eq682 (σ x) (σ y)
       grind)
    | (have r₁ := eq818
       have r₂ := eq682 x y
       grind)
    | (have r₁ := eq818
       have r₂ := eq682 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq818
       have r₂ := eq682 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq818 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq818
  have eq856 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq855
  have eq861 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq856
       grind)
    | exact superpose eq856 eq16
    | exact resolve eq16 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq862 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq861
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq861
    | exact resolve eq861 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq863 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq862
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq862
    | exact resolve eq862 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq864 : (σ x) = (σ y) := by grind
  clear eq863
  have eq865 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq16
    | exact resolve eq16 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq10
    | exact resolve eq10 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq903 : x = y := by
    first
    | (have i₁ := eq866
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq866
    | exact resolve eq866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq904 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq865
       have i₂ := eq76 (σ x)
       grind)
    | exact superpose eq76 eq865
    | exact resolve eq865 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq905 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq904
       have i₂ := eq903
       grind)
    | exact superpose eq903 eq904
    | exact resolve eq904 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq904
  have eq906 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq905
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq905
    | exact resolve eq905 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq905
  have eq907 : False := by grind
  exact eq907

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation418 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law418 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
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
  have eq168 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq170 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq838 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq987 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq170 X0 X1
       grind)
    | exact superpose eq170 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq170 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq170 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq170 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq13 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq998 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq987 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq999 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq998 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq2621 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq999 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq999
    | exact resolve eq999 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq2663 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2621 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2621
    | (have j0 := eq2621 X0 X1
       grind)
    | exact resolve eq2621 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq2700 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq2663 X1 X0
       grind)
    | exact superpose eq2663 eq10
    | (have j1 := eq2663 X1 X0
       grind)
    | exact resolve eq10 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2740 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2700 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2700
    | (have j0 := eq2700 X0 X1
       grind)
    | exact resolve eq2700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2700
  have eq2782 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq2740 X0 (σ X1)
       grind)
    | exact superpose eq2740 eq37
    | (have j1 := eq2740 X0 (σ X1)
       grind)
    | exact resolve eq37 eq2740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2740
  have eq5383 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2782 (σ X0) X1
       grind)
    | exact superpose eq2782 eq28
    | (have j1 := eq2782 (σ X0) X1
       grind)
    | exact resolve eq28 eq2782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2782
  have eq5444 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5383 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5383
    | (have j0 := eq5383 X0 X1
       grind)
    | exact resolve eq5383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5383
  have eq5482 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5444 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5444
    | (have j0 := eq5444 X0 X1
       grind)
    | exact resolve eq5444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5444
  have eq5496 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5482 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5482
    | (have j0 := eq5482 X0 X1
       grind)
    | exact resolve eq5482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482
  have eq5713 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq5496 X1 X0
       grind)
    | exact superpose eq5496 eq11
    | (have j1 := eq5496 X1 X0
       grind)
    | exact resolve eq11 eq5496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5496
  have eq6757 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5713 y x
       grind)
    | exact superpose eq5713 eq16
    | (have j1 := eq5713 y x
       grind)
    | exact resolve eq16 eq5713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5713
  have eq6819 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6757
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq6757
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq6757
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6757
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6757 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6820 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq6757
       have i₂ := eq2663 y x
       grind)
    | exact superpose eq2663 eq6757
    | (have j1 := eq2663 y x
       grind)
    | (have r₁ := eq6757
       have r₂ := eq2663 y x
       grind)
    | (have r₁ := eq6757
       have r₂ := eq2663 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6757
       have r₂ := eq2663 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6757 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663 eq6757
  have eq6823 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6820
  have eq6824 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq6823
  have eq6825 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6819
  have eq6826 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6825
  have eq6830 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6824
       grind)
    | exact superpose eq6824 eq16
    | exact resolve eq16 eq6824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6824
  have eq6831 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6830
       have r₂ := eq22 x
       grind)
    | exact resolve eq6830 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830
  have eq6835 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq838 x y
       have i₂ := eq6831
       grind)
    | exact superpose eq6831 eq838
    | (have j0 := eq838 x y
       grind)
    | exact resolve eq838 eq6831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq6831
  have eq6842 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6835
  have eq6843 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6842
  have eq6847 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6826
       grind)
    | exact superpose eq6826 eq16
    | exact resolve eq16 eq6826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6826
  have eq6848 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6847
       have r₂ := eq22 x
       grind)
    | exact resolve eq6847 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6847
  have eq6897 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6843
       grind)
    | exact superpose eq6843 eq16
    | exact resolve eq16 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6843
  have eq6933 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6897
       have i₂ := eq6848
       grind)
    | exact superpose eq6848 eq6897
    | exact resolve eq6897 eq6848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6848 eq6897
  have eq6934 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq6933
  have eq6935 : (σ x) = (σ y) := by grind
  clear eq6934
  have eq6936 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6935
       grind)
    | exact superpose eq6935 eq16
    | exact resolve eq16 eq6935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6937 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6935
       grind)
    | exact superpose eq6935 eq10
    | exact resolve eq10 eq6935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6935
  have eq6988 : x = y := by
    first
    | (have i₁ := eq6937
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6937
    | exact resolve eq6937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6937
  have eq6989 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq6936
       have i₂ := eq110 (σ x)
       grind)
    | exact superpose eq110 eq6936
    | exact resolve eq6936 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6936
  have eq6993 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6989
       have i₂ := eq6988
       grind)
    | exact superpose eq6988 eq6989
    | exact resolve eq6989 eq6988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6988 eq6989
  have eq6996 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6993
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq6993
    | exact resolve eq6993 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq6993
  have eq6997 : False := by grind
  exact eq6997

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_x_pyx_x_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq344 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq346 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       have j1 := eq345 X0 X1
       grind)
    | (have r₁ := eq344 X0 X1
       have r₂ := eq345 X0 X1
       grind)
    | exact resolve eq344 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq345
  have eq388 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq346
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq346 y (σ x)
       grind)
    | exact superpose eq346 eq16
    | (have j1 := eq346 y (σ x)
       grind)
    | exact resolve eq16 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq405 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq392
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq392
    | exact resolve eq392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq419 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq388 X0 X1
       grind)
    | exact superpose eq388 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq388 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq388 X0 X1
       grind)
    | exact resolve eq13 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq419 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq429 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq425 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq425 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq446 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq429 X1 (τ X0)
       grind)
    | exact superpose eq429 eq18
    | (have j1 := eq429 X1 (τ X0)
       grind)
    | exact resolve eq18 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq463 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq429 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq446 X1 (τ X0)
       grind)
    | exact superpose eq446 eq17
    | (have j1 := eq446 X1 (τ X0)
       grind)
    | exact resolve eq17 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq446
  have eq715 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq708
    | (have j0 := eq708 X0 X1
       grind)
    | exact resolve eq708 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq730 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq733 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq730 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq730
    | (have j0 := eq730 X0 X1
       grind)
    | exact resolve eq730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq790 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 X1
       have i₂ := eq429 X0 X1
       grind)
    | exact superpose eq429 eq733
    | (have j0 := eq733 X1 X0
       have j1 := eq429 X1 X0
       grind)
    | exact resolve eq733 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq733
  have eq853 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq790 X0 X1
       have j1 := eq463 X1 X0
       grind)
    | (have r₁ := eq790 X1 X0
       have r₂ := eq463 X0 X1
       grind)
    | exact resolve eq790 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq790
  have eq903 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq853 X1 (σ X0)
       grind)
    | exact superpose eq853 eq28
    | (have j1 := eq853 X1 (σ X0)
       grind)
    | exact resolve eq28 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq853
  have eq922 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq903 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq903
    | (have j0 := eq903 X0 X1
       grind)
    | exact resolve eq903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq948 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq922
    | (have j0 := eq922 X0 X1
       grind)
    | exact resolve eq922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq948 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq948
    | exact resolve eq948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1256 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1188 x y
       grind)
    | exact superpose eq1188 eq16
    | (have j1 := eq1188 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1188 x y
       grind)
    | exact resolve eq16 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1273 : y = (k y x) := by grind
  clear eq1256
  have eq1385 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq405
       have i₂ := eq388 y x
       grind)
    | exact superpose eq388 eq405
    | (have j1 := eq388 y x
       grind)
    | exact resolve eq405 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1386 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq1385
  have eq1387 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1386
       have i₂ := eq1273
       grind)
    | exact superpose eq1273 eq1386
    | exact resolve eq1386 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1388 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1387
       have i₂ := eq1273
       grind)
    | exact superpose eq1273 eq1387
    | exact resolve eq1387 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1389 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq405
       have i₂ := eq1388
       grind)
    | exact superpose eq1388 eq405
    | exact resolve eq405 eq1388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq1388
  have eq1399 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1389
  have eq1400 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1399
       have i₂ := eq1273
       grind)
    | exact superpose eq1273 eq1399
    | exact resolve eq1399 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1401 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1400
  have eq1403 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1401
       grind)
    | exact superpose eq1401 eq16
    | exact resolve eq16 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1427 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1403
       have i₂ := eq388 y x
       grind)
    | exact superpose eq388 eq1403
    | (have j1 := eq388 y x
       grind)
    | exact resolve eq1403 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq1428 : (M.op x y) = (k y x) := by grind
  clear eq1427
  have eq1430 : y = (M.op x y) := by
    first
    | (have i₁ := eq1428
       have i₂ := eq1273
       grind)
    | exact superpose eq1273 eq1428
    | exact resolve eq1428 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273 eq1428
  have eq1431 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1403
       have i₂ := eq1430
       grind)
    | exact superpose eq1430 eq1403
    | exact resolve eq1403 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403 eq1430
  have eq1443 : False := by grind
  exact eq1443

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_pyx_x_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq29 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq47 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq31
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 x
       have i₂ := eq82 x x
       grind)
    | exact superpose eq82 eq47
    | (have j1 := eq82 X0 X0
       grind)
    | exact resolve eq47 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq437 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq442 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq437 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq437
    | (have j0 := eq437 X0
       grind)
    | exact resolve eq437 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq463 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (σ (k X2 (M.op (τ X1) X0))) ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op (τ X1) X0)
       have i₂ := eq89 X1 X0
       grind)
    | exact superpose eq89 eq15
    | (have j1 := eq89 X1 X0
       grind)
    | exact resolve eq15 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq495 : ∀ X0 X1 X2 : G, (M.op (τ X1) X0) = X0 ∨ (σ (k X2 (k X0 (τ X1)))) = (σ (k X2 (M.op (τ X1) X0))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq474 X0 X1 X2
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq474
    | (have j0 := eq474 X0 X1 X2
       grind)
    | exact resolve eq474 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq474
  have eq502 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq463 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq463
    | (have j0 := eq463 X0 X1
       grind)
    | exact resolve eq463 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq506 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq502 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq502
    | (have j0 := eq502 (τ X1) (τ X0)
       grind)
    | exact resolve eq502 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq506 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq506
    | (have j0 := eq506 X0 X1
       grind)
    | exact resolve eq506 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq4428 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    grind
  clear eq442
  have eq4452 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 (k X0 X0)) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4428 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4428
    | (have j0 := eq4428 X0
       grind)
    | exact resolve eq4428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4428
  have eq8438 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (σ (k X1 (k (τ X0) (τ X0)))) = (σ (k X1 (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq495 (τ X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq8439 : ∀ X0 X1 : G, (σ (k X1 (k (τ X0) (τ X0)))) = (σ (k X1 (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq8438 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8438
  have eq8445 : ∀ X0 X1 : G, (σ (k X1 (M.op (τ X0) (τ X0)))) = (σ (k X1 (τ (k X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8439 X0 X1
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq8439
    | (have j0 := eq8439 X0 X1
       grind)
    | exact resolve eq8439 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8439
  have eq8467 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (k X1 (M.op (τ X0) (τ X0)))) = (k (σ X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8445 X0 X1
       have i₂ := eq19 (k X0 X0) X1
       grind)
    | exact superpose eq19 eq8445
    | (have j0 := eq8445 X0 X1
       grind)
    | exact resolve eq8445 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8445
  have eq16230 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (M.op X0 X0))) = (k (σ X1) (k (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8467 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8467
    | exact resolve eq8467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8467
  have eq16312 : ∀ X0 X1 : G, (σ (k X1 (k (τ (σ X0)) X0))) = (σ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16230 X0 X1
       have i₂ := eq23 (σ X0) X0 X1
       grind)
    | exact superpose eq23 eq16230
    | (have j0 := eq16230 X0 X1
       grind)
    | exact resolve eq16230 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16230
  have eq16319 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (k X0 X0))) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16312 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16312
    | (have j0 := eq16312 X0 X1
       grind)
    | exact resolve eq16312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16312
  have eq16519 : ∀ X0 X1 : G, (σ (k X1 (k X0 X0))) = (σ (k X1 (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq16319
  have eq16696 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = (τ (σ (k X0 (M.op X1 X1)))) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (k X1 X1))
       have i₂ := eq16519 X1 X0
       grind)
    | exact superpose eq16519 eq10
    | (have j1 := eq16519 X1 X1
       grind)
    | exact resolve eq10 eq16519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16519
  have eq16779 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16696 X0 X1
       have i₂ := eq10 (k X0 (M.op X1 X1))
       grind)
    | exact superpose eq10 eq16696
    | (have j0 := eq16696 X0 X1
       grind)
    | exact resolve eq16696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16696
  have eq17177 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (k X1 (k (τ X0) (τ X0))) = (k X1 (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq16779 X1 (τ X0)
       grind)
    | exact superpose eq16779 eq18
    | (have j1 := eq16779 X1 (τ X0)
       grind)
    | exact resolve eq18 eq16779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16779
  have eq17243 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (k X1 (k (τ X0) (τ X0))) = (k X1 (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17177 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17177
    | (have j0 := eq17177 X0 X1
       grind)
    | exact resolve eq17177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17177
  have eq17307 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (k X1 (M.op (τ X0) (τ X0))) = (k X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17243 X0 X1
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq17243
    | (have j0 := eq17243 X0 X1
       grind)
    | exact resolve eq17243 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17243
  have eq23408 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (k X0 (k X0 X0)) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq4452 X0
       grind)
    | exact superpose eq4452 eq47
    | (have j1 := eq4452 X0
       grind)
    | exact resolve eq47 eq4452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq4452
  have eq23522 : ∀ X0 : G, (k X0 (k X0 X0)) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (k X0 (k X0 X0)) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23408 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq23408
    | (have j0 := eq23408 X0
       grind)
    | exact resolve eq23408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23408
  have eq23523 : ∀ X0 : G, (k X0 (k X0 X0)) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq23522 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23522
  have eq23836 : ∀ X0 : G, (k (τ X0) (k (τ X0) (τ X0))) = (τ (M.op (k X0 (σ (τ X0))) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23523 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq23523
    | exact resolve eq23523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq23899 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ (k X0 X0)) (σ X0))
       have i₂ := eq23523 X0
       grind)
    | exact superpose eq23523 eq11
    | exact resolve eq11 eq23523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23523
  have eq24023 : ∀ X0 : G, (k (τ X0) (k (τ X0) (τ X0))) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq23836 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23836
    | exact resolve eq23836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23836
  have eq24054 : ∀ X0 : G, (k (τ X0) (τ (k X0 X0))) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq24023 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq24023
    | exact resolve eq24023 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24023
  have eq24074 : ∀ X0 : G, (τ (k X0 (k X0 X0))) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq24054 X0
       have i₂ := eq35 (k X0 X0) X0
       grind)
    | exact superpose eq35 eq24054
    | exact resolve eq24054 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24054
  have eq24149 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (τ (M.op (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (k X0 X0))
       have i₂ := eq24074 X0
       grind)
    | exact superpose eq24074 eq11
    | exact resolve eq11 eq24074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24332 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24149 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq24149
    | exact resolve eq24149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24149
  have eq24517 : ∀ X0 : G, (k (τ X0) (τ (k X0 X0))) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq24332 (τ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq24332
    | exact resolve eq24332 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24684 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24517 X0
       have i₂ := eq35 (k X0 X0) X0
       grind)
    | exact superpose eq35 eq24517
    | exact resolve eq24517 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24517
  have eq24750 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq24684 X0
       have i₂ := eq24074 X0
       grind)
    | exact superpose eq24074 eq24684
    | exact resolve eq24684 eq24074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24074 eq24684
  have eq24856 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (k (σ X0) (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq23899 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23899
    | exact resolve eq23899 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23899
  have eq25060 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq24856 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq24856
    | exact resolve eq24856 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24856
  have eq25108 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (M.op (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq25060 X0
       have i₂ := eq24332 X0
       grind)
    | exact superpose eq24332 eq25060
    | exact resolve eq25060 eq24332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25060
  have eq29043 : ∀ X0 : G, (M.op (σ (σ (k (τ X0) (τ X0)))) (σ X0)) = (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq25108 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25108
    | exact resolve eq25108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25108
  have eq29160 : ∀ X0 : G, (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) = (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq29043 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq29043
    | exact resolve eq29043 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29043
  have eq29203 : ∀ X0 : G, (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) = (σ (σ (τ (M.op (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq29160 X0
       have i₂ := eq24750 X0
       grind)
    | exact superpose eq24750 eq29160
    | exact resolve eq29160 eq24750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24750 eq29160
  have eq29236 : ∀ X0 : G, (σ (M.op (k X0 X0) X0)) = (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29203 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq29203
    | exact resolve eq29203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29203
  have eq29258 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq29236 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq29236
    | exact resolve eq29236 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29236
  have eq79034 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (k X1 (M.op X0 X0)) = (k X1 (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17307 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17307
    | exact resolve eq17307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17307
  have eq79362 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = (k X1 (τ (k (σ X0) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq79034 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq79034
    | (have j0 := eq79034 X0 X1
       grind)
    | exact resolve eq79034 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79034
  have eq79431 : ∀ X0 X1 : G, (k X1 (k (τ (σ X0)) X0)) = (k X1 (M.op X0 X0)) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79362 X0 X1
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq79362
    | (have j0 := eq79362 X0 X1
       grind)
    | exact resolve eq79362 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79362
  have eq79473 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X1 (k X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79431 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79431
    | (have j0 := eq79431 X0 X1
       grind)
    | exact resolve eq79431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79431
  have eq80278 : ∀ X0 X1 X2 : G, (k (τ X1) (k X0 X0)) = (τ (k X1 (σ (M.op X0 X0)))) ∨ (k X2 (k X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (k X0 X0)
       have i₂ := eq79473 X0 X2
       grind)
    | exact superpose eq79473 eq25
    | (have j1 := eq79473 X0 X2
       grind)
    | exact resolve eq25 eq79473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79473
  have eq80477 : ∀ X0 X1 X2 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (k X2 (k X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80278 X0 X1 X2
       have i₂ := eq25 X1 (M.op X0 X0)
       grind)
    | exact superpose eq25 eq80278
    | (have j0 := eq80278 X0 X1 (τ X1)
       grind)
    | exact resolve eq80278 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq80278
  have eq114556 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) ≠ (k (τ X0) (M.op X1 X1)) ∨ (k (τ X0) (M.op X1 X1)) = (k (τ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80477 X1 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80477
  have eq114557 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (k (τ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq114556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114556
  have eq114766 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq114557 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114557
    | exact resolve eq114557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114557
  have eq115996 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24332 X0
       have i₂ := eq114766 X0 X0
       grind)
    | exact superpose eq114766 eq24332
    | exact resolve eq24332 eq114766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24332 eq114766
  have eq116360 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    grind
  clear eq115996
  have eq866886 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq553 X0 X1
       grind)
    | exact superpose eq553 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq553 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq553 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X1)
       have r₂ := eq553 X1 X1
       grind)
    | exact resolve eq13 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866944 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq553 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq866945 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq866944 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866944
  have eq866946 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq866886 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866886
  have eq866947 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq866946 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866946
  have eq866966 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq866947 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq866947
    | (have j0 := eq866947 X0 X1
       grind)
    | exact resolve eq866947 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq866947
  have eq869563 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq866945 X0
       grind)
    | exact superpose eq866945 eq34
    | (have j1 := eq866945 X0
       grind)
    | exact resolve eq34 eq866945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq866945
  have eq869971 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq869563 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq869563
    | (have j0 := eq869563 X0
       grind)
    | exact resolve eq869563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869563
  have eq869972 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq869971 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869971
  have eq870233 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq869972 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq869972
    | exact resolve eq869972 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870427 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq869972 X0
       grind)
    | exact superpose eq869972 eq10
    | exact resolve eq10 eq869972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869972
  have eq871416 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq870233 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq870233
    | exact resolve eq870233 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870233
  have eq875262 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq29258 X0
       have i₂ := eq871416 X0
       grind)
    | exact superpose eq871416 eq29258
    | exact resolve eq29258 eq871416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29258
  have eq875355 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq871416 X0
       grind)
    | exact superpose eq871416 eq10
    | exact resolve eq10 eq871416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq876242 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq875355 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq875355
    | exact resolve eq875355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875355
  have eq876288 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq875262 X0
       have i₂ := eq116360 X0
       grind)
    | exact superpose eq116360 eq875262
    | exact resolve eq875262 eq116360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116360 eq875262
  have eq878084 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq876242 (σ X0)
       grind)
    | exact superpose eq876242 eq15
    | exact resolve eq15 eq876242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878444 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq878084 X0
       have i₂ := eq871416 X0
       grind)
    | exact superpose eq871416 eq878084
    | exact resolve eq878084 eq871416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871416 eq878084
  have eq1141194 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq866966 X0 X1
       grind)
    | exact superpose eq866966 eq11
    | (have j1 := eq866966 X0 X1
       grind)
    | exact resolve eq11 eq866966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866966
  have eq1141750 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1141194 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1141194
    | (have j0 := eq1141194 X0 X1
       grind)
    | exact resolve eq1141194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141194
  have eq1142304 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X0)) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1141750 X0 X1
       have i₂ := eq870427 X0
       grind)
    | exact superpose eq870427 eq1141750
    | (have j0 := eq1141750 X0 X1
       grind)
    | exact resolve eq1141750 eq870427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870427 eq1141750
  have eq1142832 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1142304 X0 X1
       have i₂ := eq876242 X0
       grind)
    | exact superpose eq876242 eq1142304
    | (have j0 := eq1142304 X0 X1
       grind)
    | exact resolve eq1142304 eq876242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876242 eq1142304
  have eq1159316 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1142832 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1142832
    | (have j0 := eq1142832 X1 (σ X0)
       grind)
    | exact resolve eq1142832 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142832
  have eq1168342 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1159316 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1159316
    | (have j0 := eq1159316 X1 (σ X0)
       grind)
    | exact resolve eq1159316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159316
  have eq1169569 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1168342 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1168342
    | (have j0 := eq1168342 X0 X1
       grind)
    | exact resolve eq1168342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168342
  have eq1170119 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1169569 X0 X1
       have i₂ := eq878444 X0
       grind)
    | exact superpose eq878444 eq1169569
    | (have j0 := eq1169569 X0 X1
       grind)
    | exact resolve eq1169569 eq878444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169569
  have eq1170599 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1170119 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1170119
    | (have j0 := eq1170119 X0 X1
       grind)
    | exact resolve eq1170119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170119
  have eq1175342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq202
       have i₂ := eq1170599 y x
       grind)
    | exact superpose eq1170599 eq202
    | (have j1 := eq1170599 y x
       grind)
    | (have r₁ := eq202
       have r₂ := eq1170599 y x
       grind)
    | exact resolve eq202 eq1170599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq1170599
  have eq1175894 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq1175342
  have eq1176328 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq207 x y
       grind)
    | (have r₁ := eq1175894
       have r₂ := eq207 x y
       grind)
    | exact resolve eq1175894 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq1175894
  have eq1176908 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1176328
       have i₂ := eq878444 y
       grind)
    | exact superpose eq878444 eq1176328
    | exact resolve eq1176328 eq878444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176328
  have eq1186461 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1176908
       grind)
    | exact superpose eq1176908 eq16
    | exact resolve eq16 eq1176908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186487 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1176908
       grind)
    | exact superpose eq1176908 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1176908
       grind)
    | exact resolve eq13 eq1176908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176908
  have eq1186571 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1186487
  have eq1186621 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1186571
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1186571
    | exact resolve eq1186571 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186571
  have eq1186665 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1186621
       have i₂ := eq878444 y
       grind)
    | exact superpose eq878444 eq1186621
    | exact resolve eq1186621 eq878444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878444 eq1186621
  have eq1186666 : x = (M.op y y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1186665
  have eq1191879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq876288 y
       have i₂ := eq1186666
       grind)
    | exact superpose eq1186666 eq876288
    | exact resolve eq876288 eq1186666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186666
  have eq1191978 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1191879
       have r₂ := eq16
       grind)
    | exact resolve eq1191879 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191879
  have eq1195313 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq502 x y
       have i₂ := eq1191978
       grind)
    | exact superpose eq1191978 eq502
    | (have j0 := eq502 x y
       grind)
    | exact resolve eq502 eq1191978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq1191978
  have eq1196404 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1195313
       have r₂ := eq1186461
       grind)
    | exact resolve eq1195313 eq1186461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195313
  have eq1204572 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1186461
       have i₂ := eq1196404
       grind)
    | exact superpose eq1196404 eq1186461
    | exact resolve eq1186461 eq1196404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186461 eq1196404
  have eq1204666 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1204572
  have eq1204667 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1204666
  have eq1207201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq876288 y
       have i₂ := eq1204667
       grind)
    | exact superpose eq1204667 eq876288
    | exact resolve eq876288 eq1204667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204667
  have eq1207304 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1207201
       have r₂ := eq16
       grind)
    | exact resolve eq1207201 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207201
  have eq1207566 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1207304
       grind)
    | exact superpose eq1207304 eq10
    | exact resolve eq10 eq1207304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207304
  have eq1208557 : x = (M.op y y) := by
    first
    | (have i₁ := eq1207566
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1207566
    | exact resolve eq1207566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207566
  have eq1212313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq876288 y
       have i₂ := eq1208557
       grind)
    | exact superpose eq1208557 eq876288
    | exact resolve eq876288 eq1208557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876288 eq1208557
  have eq1212417 : False := by grind
  exact eq1212417

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_pyy_pxy_Equation419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 (k X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq32 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq36 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq37 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq42
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq45 X0 (M.op X1 X1)
       have r₂ := eq38 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq38 (k X1 X1) X1
       grind)
    | exact resolve eq45 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq45
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq48
  have eq112 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq116 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       have j1 := eq51 X0 X1
       grind)
    | (have r₁ := eq112 X0 X1
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq112 X0 X0
       have r₂ := eq51 X0 X0
       grind)
    | exact resolve eq112 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq112
  have eq263 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq116 (σ X0) (σ X1)
       grind)
    | exact superpose eq116 eq15
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq263
    | exact resolve eq263 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq263
  have eq273 : False := by grind
  exact eq273
