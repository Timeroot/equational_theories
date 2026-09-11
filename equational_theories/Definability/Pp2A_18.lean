import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq26 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 x X0
       have i₂ := eq26 x X1
       grind)
    | exact superpose eq26 eq26
    | exact resolve eq26 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ X2 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) X1
       have r₂ := eq26 X0 X1
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq49
    | (have j0 := eq49 X0 X1 X2
       grind)
    | (have r₁ := eq49 X0 X1 (M.op X0 X0)
       have r₂ := eq36 X0 X0
       grind)
    | exact resolve eq49 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq49
  have eq117 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq32 X0 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq121 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq121 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq128 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq132 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq128 X0 X1
       have j1 := eq52 X0 X0 X1
       grind)
    | (have r₁ := eq128 X0 x
       have r₂ := eq52 X0 X1 x
       grind)
    | (have r₁ := eq128 X0 (M.op X0 X0)
       have r₂ := eq52 X0 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq128 X0 X0
       have r₂ := eq52 X0 X1 (k X0 X0)
       grind)
    | exact resolve eq128 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq136 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X2) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq117 X0 X1 X2
       have j1 := eq52 X0 X1 X0
       grind)
    | (have r₁ := eq117 X0 X0 X2
       have r₂ := eq52 X0 X1 (M.op X2 X2)
       grind)
    | (have r₁ := eq117 X0 X1 X0
       have r₂ := eq52 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq117 X0 X0 X2
       have r₂ := eq52 X0 X1 (k X0 X0)
       grind)
    | exact resolve eq117 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq117
  have eq575 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq132 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq578 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq575 X0 X1
       have j1 := eq136 X0 X1 x
       grind)
    | (have r₁ := eq575 x x
       have r₂ := eq136 x x x
       grind)
    | (have r₁ := eq575 X0 X1
       have r₂ := eq136 X0 X1 X0
       grind)
    | exact resolve eq575 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq575
  have eq600 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq578 (σ X0) (σ X1)
       grind)
    | exact superpose eq578 eq15
    | exact resolve eq15 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq578 X0 X1
       grind)
    | exact superpose eq578 eq600
    | exact resolve eq600 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq600
  have eq3868 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq603 x y
       grind)
    | exact superpose eq603 eq16
    | (have r₁ := eq16
       have r₂ := eq603 x y
       grind)
    | exact resolve eq16 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq3928 : False := by grind
  exact eq3928

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = X2 ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq14
    | (have j0 := eq14 X2 X2
       grind)
    | exact resolve eq14 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq100 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq90 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq90 X0 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq90 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq304 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (k X4 X1) = (M.op X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq25 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq21 x X1 x X0
       grind)
    | exact superpose eq21 eq25
    | (have j0 := eq25 X0 X1 x X4
       grind)
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq315 : ∀ X1 X4 : G, (k X4 X1) = (M.op X4 X1) := by
    intro X1 X4
    first
    | (have j0 := eq304 x X1 X4
       have j1 := eq100 x X4 X1
       grind)
    | (have r₁ := eq304 x x X4
       have r₂ := eq100 x X1 x
       grind)
    | (have r₁ := eq304 x (M.op x (M.op x x)) X4
       have r₂ := eq100 x X1 (M.op x (M.op x x))
       grind)
    | (have r₁ := eq304 X1 (k X1 (M.op X1 X1)) X4
       have r₂ := eq100 x X1 (M.op X1 X1)
       grind)
    | exact resolve eq304 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq304
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq315 (σ X1) (σ X0)
       grind)
    | exact superpose eq315 eq15
    | exact resolve eq15 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq315 X1 X0
       grind)
    | exact superpose eq315 eq590
    | exact resolve eq590 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq590
  have eq598 : False := by grind
  exact eq598

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pyy_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X2 ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = X0 ∨ (M.op X3 X3) = X0 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X3 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X3 : G, (M.op X3 X3) = X0 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X3
    first
    | (have j0 := eq33 X0 x x X3
       have j1 := eq25 X0 x X0 X3
       grind)
    | (have r₁ := eq33 x X0 x X3
       have r₂ := eq25 X0 x x X3
       grind)
    | (have r₁ := eq33 (M.op X0 (M.op x (M.op X0 (M.op X3 X3)))) x x X3
       have r₂ := eq25 X0 x (M.op X3 X3) X3
       grind)
    | exact resolve eq33 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq33
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq67 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq104 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 x x X2
       have i₂ := eq46 X0 x
       grind)
    | (have i₁ := eq23 X0 X1 X2
       have i₂ := eq46 (M.op X1 X0) x
       grind)
    | exact superpose eq46 eq23
    | (have j1 := eq46 (M.op X2 X0) X0
       grind)
    | exact resolve eq23 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq46
  have eq242 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq244 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq242 X0 X1
       have j1 := eq104 X1 X0 x
       grind)
    | (have r₁ := eq242 x X0
       have r₂ := eq104 X0 X1 x
       grind)
    | (have r₁ := eq242 X0 X0
       have r₂ := eq104 X0 X1 X0
       grind)
    | exact resolve eq242 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq242
  have eq622 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq244 (σ X0) (σ X1)
       grind)
    | exact superpose eq244 eq15
    | exact resolve eq15 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq244 X0 X1
       grind)
    | exact superpose eq244 eq622
    | exact resolve eq622 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq622
  have eq631 : False := by grind
  exact eq631

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pxy_Equation335 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law335 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0) (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq19
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq112
    | exact resolve eq112 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq112
  have eq356 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq358 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq361 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq356
    | (have j0 := eq356 X0 X1
       grind)
    | exact resolve eq356 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq797 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq361 x y
       grind)
    | exact superpose eq361 eq16
    | (have j1 := eq361 x y
       grind)
    | exact resolve eq16 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq3321 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq358 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq358
    | exact resolve eq358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq3382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3321 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3321
    | (have j0 := eq3321 X0 X1
       grind)
    | exact resolve eq3321 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq7386 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq797
       have i₂ := eq3382 x y
       grind)
    | exact superpose eq3382 eq797
    | (have j1 := eq3382 x y
       grind)
    | (have r₁ := eq797
       have r₂ := eq3382 x y
       grind)
    | (have r₁ := eq797
       have r₂ := eq3382 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq797
       have r₂ := eq3382 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq797 eq3382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq3382
  have eq7387 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq7386
  have eq10763 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7387
       grind)
    | exact superpose eq7387 eq16
    | exact resolve eq16 eq7387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7387
  have eq10764 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq10763
       have r₂ := eq24 x
       grind)
    | exact resolve eq10763 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10763
  have eq10766 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10764
       grind)
    | exact superpose eq10764 eq10
    | exact resolve eq10 eq10764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10764
  have eq10818 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10766
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10766
    | exact resolve eq10766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10766
  have eq10820 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10818
       grind)
    | exact superpose eq10818 eq16
    | exact resolve eq16 eq10818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10818
  have eq10821 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10820
       have r₂ := eq24 x
       grind)
    | exact resolve eq10820 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10820
  have eq10838 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq10821
       grind)
    | exact superpose eq10821 eq10
    | exact resolve eq10 eq10821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10821
  have eq10899 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10838
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10838
    | exact resolve eq10838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10838
  have eq10900 : x = (M.op y y) := by grind
  clear eq10899
  have eq10912 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117 y
       have i₂ := eq10900
       grind)
    | exact superpose eq10900 eq117
    | exact resolve eq117 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq10967 : x = (M.op y x) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq10900
       grind)
    | exact superpose eq10900 eq9
    | exact resolve eq9 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10968 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq10900
       grind)
    | exact superpose eq10900 eq19
    | exact resolve eq19 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq10900
  have eq11067 : x = (M.op x y) := by
    first
    | (have i₁ := eq10967
       have i₂ := eq10968
       grind)
    | exact superpose eq10968 eq10967
    | exact resolve eq10967 eq10968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10967 eq10968
  have eq11599 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10912
       grind)
    | exact superpose eq10912 eq16
    | exact resolve eq16 eq10912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10912
  have eq11619 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11599
       have i₂ := eq11067
       grind)
    | exact superpose eq11067 eq11599
    | exact resolve eq11599 eq11067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11067 eq11599
  have eq11620 : False := by grind
  exact eq11620

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pxx_pyx_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq262 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq262 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq262 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq262 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq274 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq263 (σ X0)
       grind)
    | exact superpose eq263 eq15
    | exact resolve eq15 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq263 X0
       grind)
    | exact superpose eq263 eq274
    | exact resolve eq274 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq274
  have eq337 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq9
    | exact resolve eq9 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X2 (M.op X0 X0))) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X1 X1) = (k X1 X2) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X2) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq443 X0 X1 X2
       have j1 := eq478 X2 X0
       grind)
    | (have r₁ := eq443 (M.op X1 X1) X1 X2
       have r₂ := eq478 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq443 X0 (M.op X0 X0) X2
       have r₂ := eq478 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq443 X1 X1 X0
       have r₂ := eq478 X0 X1
       grind)
    | exact resolve eq443 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq478
  have eq510 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq440 X0 X1 X2
       have i₂ := eq9 X0 X2
       grind)
    | exact superpose eq9 eq440
    | (have j0 := eq440 X0 X1 X2
       grind)
    | exact resolve eq440 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq3756 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq508 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq4051 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3756 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq4059 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4051 X0 X1
       have j1 := eq510 X0 X1 x
       grind)
    | (have r₁ := eq4051 x X0
       have r₂ := eq510 X0 x x
       grind)
    | (have r₁ := eq4051 x X1
       have r₂ := eq510 x X1 x
       grind)
    | exact resolve eq4051 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq4051
  have eq4308 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq4059 X2 X0
       grind)
    | exact superpose eq4059 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq4059 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq4059 X0 X1
       grind)
    | exact resolve eq12 eq4059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4312 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq4059 X2 X0
       grind)
    | exact superpose eq4059 eq337
    | (have j0 := eq337 X0 X1
       have j1 := eq4059 X2 X0
       grind)
    | exact resolve eq337 eq4059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0
       have i₂ := eq4059 X1 (σ X0)
       grind)
    | exact superpose eq4059 eq293
    | (have j1 := eq4059 X1 (σ X0)
       grind)
    | exact resolve eq293 eq4059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq4381 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq4059 (τ X1) X0
       grind)
    | exact superpose eq4059 eq17
    | (have j1 := eq4059 X0 X0
       grind)
    | exact resolve eq17 eq4059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4059
  have eq4427 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4312 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4312
  have eq4428 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4308 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4308
  have eq4572 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq4428 X1 (τ X0) X2
       grind)
    | exact superpose eq4428 eq17
    | (have j1 := eq4428 X1 X1 X2
       grind)
    | exact resolve eq17 eq4428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4428
  have eq5260 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4381 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4381
    | (have j0 := eq4381 X1 X1
       grind)
    | exact resolve eq4381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4381
  have eq5400 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5260 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5260
    | (have j0 := eq5260 X0 X1
       grind)
    | exact resolve eq5260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5260
  have eq6429 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq4345 X0 X1
       grind)
    | exact superpose eq4345 eq10
    | (have j1 := eq4345 X0 X1
       grind)
    | exact resolve eq10 eq4345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4345
  have eq6507 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6429 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6429
    | (have j0 := eq6429 X0 X1
       grind)
    | exact resolve eq6429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6429
  have eq6579 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq6507 X0 X2
       grind)
    | exact superpose eq6507 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq6507 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq6507 X0 X1
       grind)
    | exact resolve eq12 eq6507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6635 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq6507 X0 (σ X1)
       grind)
    | exact superpose eq6507 eq15
    | (have j1 := eq6507 X0 X1
       grind)
    | exact resolve eq15 eq6507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6507
  have eq6669 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op (σ X0) X2) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6579 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6579
  have eq7341 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6635 x y
       grind)
    | exact superpose eq6635 eq16
    | (have j1 := eq6635 x x
       grind)
    | exact resolve eq16 eq6635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7505 : x = (M.op x x) := by
    first
    | (have j1 := eq5400 x x
       grind)
    | (have r₁ := eq7341
       have r₂ := eq5400 y x
       grind)
    | exact resolve eq7341 eq5400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5400 eq7341
  have eq7915 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0
       have i₂ := eq7505
       grind)
    | exact superpose eq7505 eq9
    | exact resolve eq9 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7916 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq7505
       grind)
    | exact superpose eq7505 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq7505
       grind)
    | exact resolve eq12 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7920 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq337 x X0
       have i₂ := eq7505
       grind)
    | exact superpose eq7505 eq337
    | (have j0 := eq337 x X0
       grind)
    | exact resolve eq337 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7921 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq338 x X0
       have i₂ := eq7505
       grind)
    | exact superpose eq7505 eq338
    | exact resolve eq338 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq7505
  have eq7957 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq7920 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7920
  have eq7958 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq7916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7916
  have eq8267 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq7957 (σ X0)
       grind)
    | exact superpose eq7957 eq15
    | exact resolve eq15 eq7957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7957
  have eq8303 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq8267 X0
       have i₂ := eq7958 X0
       grind)
    | exact superpose eq7958 eq8267
    | exact resolve eq8267 eq7958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7958 eq8267
  have eq9010 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ X0) (σ (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq7921 (σ X0)
       have i₂ := eq8303 X0
       grind)
    | exact superpose eq8303 eq7921
    | exact resolve eq7921 eq8303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7921 eq8303
  have eq14621 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4427 X1 (σ X0) X2
       grind)
    | exact superpose eq4427 eq15
    | (have j1 := eq4427 X1 X1 X2
       grind)
    | exact resolve eq15 eq4427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427
  have eq30229 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4572 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4572
    | (have j0 := eq4572 X0 X1 X2
       grind)
    | exact resolve eq4572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572
  have eq30697 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30229 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq30229
    | (have j0 := eq30229 X0 X1 X2
       grind)
    | exact resolve eq30229 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30229
  have eq34928 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq14621 x y X0
       grind)
    | exact superpose eq14621 eq16
    | (have j1 := eq14621 X0 y X0
       grind)
    | exact resolve eq16 eq14621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14621
  have eq35329 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq34928 X0
       have j1 := eq30697 X0 y X0
       grind)
    | (have r₁ := eq34928 X0
       have r₂ := eq30697 x y x
       grind)
    | exact resolve eq34928 eq30697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30697 eq34928
  have eq35518 : ∀ X0 X1 : G, (M.op y X0) = (M.op X0 y) ∨ (k X1 (σ y)) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6669 y X0 X1
       have i₂ := eq35329 X0
       grind)
    | exact superpose eq35329 eq6669
    | (have j0 := eq6669 y X1 X1
       grind)
    | exact resolve eq6669 eq35329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6669
  have eq42033 : ∀ X0 X1 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (M.op y X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq35518 X1 (σ X0)
       grind)
    | exact superpose eq35518 eq15
    | (have j1 := eq35518 X1 X1
       grind)
    | exact resolve eq15 eq35518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35518
  have eq42090 : ∀ X0 X1 : G, (σ (M.op y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op y X1) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq42033 X0 X1
       have i₂ := eq35329 X0
       grind)
    | exact superpose eq35329 eq42033
    | (have j0 := eq42033 X0 X1
       grind)
    | exact resolve eq42033 eq35329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42033
  have eq66781 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y (M.op y x))) ∨ (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq9010 y
       have i₂ := eq42090 (M.op y x) X0
       grind)
    | exact superpose eq42090 eq9010
    | (have j1 := eq42090 X0 X0
       grind)
    | exact resolve eq9010 eq42090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42090
  have eq67027 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq66781 X0
       have i₂ := eq7915 y
       grind)
    | exact superpose eq7915 eq66781
    | (have j0 := eq66781 X0
       grind)
    | exact resolve eq66781 eq7915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66781
  have eq67059 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq67027 X0
       grind)
    | (have r₁ := eq67027 X0
       have r₂ := eq16
       grind)
    | exact resolve eq67027 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67027
  have eq67091 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq9010 y
       have i₂ := eq67059 x
       grind)
    | exact superpose eq67059 eq9010
    | exact resolve eq9010 eq67059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9010
  have eq67092 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq7915 y
       have i₂ := eq67059 x
       grind)
    | exact superpose eq67059 eq7915
    | exact resolve eq7915 eq67059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915
  have eq74499 : (M.op (σ x) (σ y)) = (σ (k (M.op x y) y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6635 y (M.op x y)
       have i₂ := eq67091
       grind)
    | exact superpose eq67091 eq6635
    | (have j0 := eq6635 y x
       grind)
    | exact resolve eq6635 eq67091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6635 eq67091
  have eq74538 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74499
       have i₂ := eq35329 (M.op x y)
       grind)
    | exact superpose eq35329 eq74499
    | exact resolve eq74499 eq35329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74499
  have eq74557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74538
       have i₂ := eq67092
       grind)
    | exact superpose eq67092 eq74538
    | exact resolve eq74538 eq67092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67092 eq74538
  have eq74573 : y = (M.op y y) := by
    first
    | (have r₁ := eq74557
       have r₂ := eq16
       grind)
    | exact resolve eq74557 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74557
  have eq74626 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq337 y X0
       have i₂ := eq74573
       grind)
    | exact superpose eq74573 eq337
    | (have j0 := eq337 y X0
       grind)
    | exact resolve eq337 eq74573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq74573
  have eq74679 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq74626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74626
  have eq79127 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq74679 (σ X0)
       grind)
    | exact superpose eq74679 eq15
    | exact resolve eq15 eq74679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74679
  have eq79180 : ∀ X0 : G, (σ (M.op y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq79127 X0
       have i₂ := eq35329 X0
       grind)
    | exact superpose eq35329 eq79127
    | exact resolve eq79127 eq35329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35329 eq79127
  have eq79282 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79180 x
       grind)
    | exact superpose eq79180 eq16
    | exact resolve eq16 eq79180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79180
  have eq79324 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq79282
       have i₂ := eq67059 x
       grind)
    | exact superpose eq67059 eq79282
    | exact resolve eq79282 eq67059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67059 eq79282
  have eq79325 : False := by grind
  exact eq79325

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pxy_Equation3352 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq464 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq473 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq464
  have eq476 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq461
    | (have j0 := eq461 X0 X1
       grind)
    | exact resolve eq461 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq3409 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq473 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq473
    | (have j0 := eq473 (σ X0) X1
       grind)
    | exact resolve eq473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq3463 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3409 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3409
    | (have j0 := eq3409 X0 X1
       grind)
    | exact resolve eq3409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq3469 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3463 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq3463
    | (have j0 := eq3463 X0 X1
       grind)
    | exact resolve eq3463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3463
  have eq3471 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3469 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3469
    | (have j0 := eq3469 X0 X1
       grind)
    | exact resolve eq3469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469
  have eq4104 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq476 X1 X0
       grind)
    | exact superpose eq476 eq10
    | (have j1 := eq476 X1 X0
       grind)
    | exact resolve eq10 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq4526 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq4104 X1 X0
       grind)
    | exact superpose eq4104 eq11
    | (have j1 := eq4104 X1 X0
       grind)
    | exact resolve eq11 eq4104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104
  have eq4593 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4526 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq4526
    | (have j0 := eq4526 X0 X1
       grind)
    | exact resolve eq4526 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq4526
  have eq4633 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (M.op (σ X1) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4593 X0 (σ X1)
       grind)
    | exact superpose eq4593 eq15
    | (have j1 := eq4593 X0 (σ X1)
       grind)
    | exact resolve eq15 eq4593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4593
  have eq4696 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4633 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4633
    | (have j0 := eq4633 X0 X1
       grind)
    | exact resolve eq4633 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4633
  have eq4710 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4696 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq4696
    | (have j0 := eq4696 X0 X1
       grind)
    | exact resolve eq4696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4696
  have eq6141 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4710 x y
       grind)
    | exact superpose eq4710 eq16
    | (have j1 := eq4710 x y
       grind)
    | exact resolve eq16 eq4710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4710
  have eq6189 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq6141
       have i₂ := eq3471 x y
       grind)
    | exact superpose eq3471 eq6141
    | (have j1 := eq3471 x y
       grind)
    | (have r₁ := eq6141
       have r₂ := eq3471 x y
       grind)
    | (have r₁ := eq6141
       have r₂ := eq3471 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6141
       have r₂ := eq3471 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6141 eq3471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471 eq6141
  have eq6190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6189
  have eq6191 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq6190
  have eq6197 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6191
       grind)
    | exact superpose eq6191 eq16
    | exact resolve eq16 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191
  have eq6198 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6197
       have r₂ := eq22 x
       grind)
    | exact resolve eq6197 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6197
  have eq6199 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op X0 (M.op x x))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq6198
       grind)
    | exact superpose eq6198 eq9
    | exact resolve eq9 eq6198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq6234 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq6199 X0
       have i₂ := eq9 x X0
       grind)
    | exact superpose eq9 eq6199
    | exact resolve eq6199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6199
  have eq6236 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq6234 X0
       grind)
    | exact superpose eq6234 eq10
    | (have j1 := eq6234 X0
       grind)
    | exact resolve eq10 eq6234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6234
  have eq6289 : ∀ X0 : G, x = y ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq6236 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6236
    | (have j0 := eq6236 X0
       grind)
    | exact resolve eq6236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6236
  have eq6291 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq6289 X0
       grind)
    | exact superpose eq6289 eq16
    | (have j1 := eq6289 X0
       grind)
    | exact resolve eq16 eq6289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq6292 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq6291 X0
       grind)
    | (have r₁ := eq6291 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq6291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6291
  have eq6331 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq6292 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq6292 eq9
    | exact resolve eq9 eq6292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6376 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6331 X0
       have i₂ := eq6292 (M.op X0 X0)
       grind)
    | exact superpose eq6292 eq6331
    | exact resolve eq6331 eq6292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6331
  have eq6412 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq6376 X0
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq6376
    | exact resolve eq6376 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376
  have eq6430 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op X0 (σ (M.op y x)))) := by
    intro X0
    first
    | (have i₁ := eq106 y X0
       have i₂ := eq6412 y
       grind)
    | exact superpose eq6412 eq106
    | exact resolve eq106 eq6412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6479 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op X0 (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq6430 X0
       have i₂ := eq6292 x
       grind)
    | exact superpose eq6292 eq6430
    | exact resolve eq6430 eq6292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6292 eq6430
  have eq6500 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq6479 X0
       have i₂ := eq106 x X0
       grind)
    | exact superpose eq106 eq6479
    | exact resolve eq6479 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq6479
  have eq6843 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y)
       have i₂ := eq6500 (M.op (σ y) (M.op X0 X0))
       grind)
    | exact superpose eq6500 eq9
    | exact resolve eq9 eq6500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6890 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ x) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6843 X0
       have i₂ := eq6500 (M.op X0 X0)
       grind)
    | exact superpose eq6500 eq6843
    | exact resolve eq6843 eq6500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6500 eq6843
  have eq6961 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6890 X0
       have i₂ := eq9 X0 (σ x)
       grind)
    | exact superpose eq9 eq6890
    | exact resolve eq6890 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890
  have eq7230 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6961 (σ x)
       grind)
    | exact superpose eq6961 eq16
    | exact resolve eq16 eq6961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6961
  have eq7251 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7230
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq7230
    | exact resolve eq7230 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7230
  have eq7295 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7251
       have i₂ := eq6412 x
       grind)
    | exact superpose eq6412 eq7251
    | exact resolve eq7251 eq6412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6412 eq7251
  have eq7296 : False := by grind
  exact eq7296

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pyx_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
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
  clear eq36
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq14 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq54 X0 x X2
       have i₂ := eq14 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq54 X0 x X2
       have i₂ := eq14 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq79 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq77 (σ X0)
       grind)
    | exact superpose eq77 eq10
    | exact resolve eq10 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq77 sF2
       grind)
    | exact superpose eq77 eq50
    | exact resolve eq50 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq82 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq81
    | exact resolve eq81 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq79
    | exact resolve eq79 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq91 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq77 sF3
       grind)
    | exact superpose eq77 eq75
    | exact resolve eq75 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq91
    | exact resolve eq91 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq91
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  clear eq45
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq117 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq423 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) x
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq55
    | exact resolve eq55 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq13650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq13651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq13650
    | exact resolve eq13650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13650
  have eq13662 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq13651
       have r₂ := eq28
       grind)
    | exact resolve eq13651 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13651
  have eq13669 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq13662 eq117
    | exact resolve eq117 eq13662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq13662
  have eq13724 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq13669
    | exact resolve eq13669 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13669
  have eq13725 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13724
  have eq13739 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq55 y x
       have i₂ := eq13725
       grind)
    | exact superpose eq13725 eq55
    | exact resolve eq55 eq13725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq13742 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq423 y x
       have i₂ := eq13725
       grind)
    | exact superpose eq13725 eq423
    | exact resolve eq423 eq13725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq13725
  have eq13793 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13742 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13742
    | (have j0 := eq13742 X0
       grind)
    | exact resolve eq13742 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13742
  have eq13805 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13739 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13739
    | (have j0 := eq13739 x
       grind)
    | exact resolve eq13739 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13739
  have eq14000 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13805 eq30
    | exact resolve eq30 eq13805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13805
  have eq14099 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq14000
    | exact resolve eq14000 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14000
  have eq14100 : y = (M.op x y) ∨ x = y := by grind
  clear eq14099
  have eq14121 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14100 eq21
    | exact resolve eq21 eq14100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14100
  have eq14215 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14121
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14121
    | exact resolve eq14121 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14121
  have eq16786 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq13793
    | (have j0 := eq13793 (σ x)
       grind)
    | exact resolve eq13793 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13793
  have eq16873 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16786 eq28
    | exact resolve eq28 eq16786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16786
  have eq16875 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16873
       have r₂ := eq14215
       grind)
    | exact resolve eq16873 eq14215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14215 eq16873
  have eq16878 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq16875 eq30
    | exact resolve eq30 eq16875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16875
  have eq17006 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq16878
    | exact resolve eq16878 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16878
  have eq17007 : x = y := by grind
  clear eq17006
  have eq17028 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17007
       grind)
    | exact superpose eq17007 eq19
    | exact resolve eq19 eq17007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17029 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17007
       grind)
    | exact superpose eq17007 eq25
    | exact resolve eq25 eq17007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17007
  have eq17122 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17029
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17029
    | exact resolve eq17029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17029
  have eq17145 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17122 eq27
    | exact resolve eq27 eq17122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17122
  have eq17387 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17145 eq82
    | exact resolve eq82 eq17145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq17145
  have eq17430 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17387
       have i₂ := eq17028
       grind)
    | exact superpose eq17028 eq17387
    | exact resolve eq17387 eq17028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17028 eq17387
  have eq17440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17430 eq15
    | exact resolve eq15 eq17430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17430
  have eq17490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17440
    | exact resolve eq17440 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17440
  have eq17499 : False := by grind
  exact eq17499

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_x_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op (M.op X2 X1) X3) X0) = (M.op (M.op (M.op X2 X1) X3) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) X3) X0
       have i₂ := eq63 X3 X1 X0 X2
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X0 ∨ (k (M.op (M.op X2 X1) X3) X0) = (M.op (M.op (M.op X2 X1) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74 X0 X1 X2 X3
       have i₂ := eq63 X3 X1 (M.op (M.op X2 X1) X3) X2
       grind)
    | exact superpose eq63 eq74
    | (have j0 := eq74 X0 X1 X2 X3
       grind)
    | exact resolve eq74 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq281 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X1)) = X2 ∨ (M.op X2 X1) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq14 X2 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 (M.op X0 X1)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq290 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq292 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq293 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq294 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq295 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq291 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq291 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq291 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq296 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq281
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq281
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq307 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq295 (σ X0)
       grind)
    | exact superpose eq295 eq15
    | exact resolve eq15 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq307 X0
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq307
    | exact resolve eq307 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq372 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (σ X0) X1 (σ X0)
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq63
    | exact resolve eq63 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq294 (σ X1) X0
       grind)
    | exact superpose eq294 eq22
    | (have j1 := eq294 (σ X1) X0
       grind)
    | exact resolve eq22 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq768 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq294 (τ X1) X0
       grind)
    | exact superpose eq294 eq18
    | (have j1 := eq294 (τ X1) X0
       grind)
    | exact resolve eq18 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq771 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq294 (σ X1) (σ X0)
       grind)
    | exact superpose eq294 eq15
    | (have j1 := eq294 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq294 X1 (τ X0)
       grind)
    | exact superpose eq294 eq17
    | (have j1 := eq294 X1 (τ X0)
       grind)
    | exact resolve eq17 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq791 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq771 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq771
    | (have j0 := eq771 X0 X1
       grind)
    | exact resolve eq771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq826 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq292 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15527 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq768 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq768
    | exact resolve eq768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq15613 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15527 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq15527
    | (have j0 := eq15527 X0 X1
       grind)
    | exact resolve eq15527 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15527
  have eq15804 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq294 (τ X1) X0
       have i₂ := eq779 X1 X0
       grind)
    | exact superpose eq779 eq294
    | (have j0 := eq294 (τ X1) X0
       have j1 := eq779 X1 X0
       grind)
    | exact resolve eq294 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq15844 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq15804 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15804
  have eq15891 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15844 X0 X1
       have j1 := eq13 (τ X1) X0
       grind)
    | (have r₁ := eq15844 X0 X1
       have r₂ := eq13 X0 (τ X1)
       grind)
    | (have r₁ := eq15844 X1 X1
       have r₂ := eq13 (τ X1) X1
       grind)
    | exact resolve eq15844 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15844
  have eq16016 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq767 X1 X0
       grind)
    | exact superpose eq767 eq28
    | (have j1 := eq767 X1 X0
       grind)
    | exact resolve eq28 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16026 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq294 X1 (σ X0)
       have i₂ := eq767 X1 X0
       grind)
    | exact superpose eq767 eq294
    | (have j0 := eq294 X1 (σ X0)
       have j1 := eq767 X1 X0
       grind)
    | exact resolve eq294 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq767
  have eq16061 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq16026 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026
  have eq16086 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq16061 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq16061 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq16061 X0 X0
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq16061 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16061
  have eq16095 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16016 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16016
    | (have j0 := eq16016 X0 X1
       grind)
    | exact resolve eq16016 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16016
  have eq16445 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 (σ (τ X0)))) ∨ (M.op X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq16095 (τ X0) X1
       grind)
    | exact superpose eq16095 eq31
    | (have j1 := eq16095 (τ X0) X1
       grind)
    | exact resolve eq31 eq16095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16095
  have eq16516 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16445 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16445
    | (have j0 := eq16445 X0 X1
       grind)
    | exact resolve eq16445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16445
  have eq16560 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16516 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq16516
    | (have j0 := eq16516 X0 X1
       grind)
    | exact resolve eq16516 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16516
  have eq16591 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16560 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16560
    | (have j0 := eq16560 X0 X1
       grind)
    | exact resolve eq16560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16560
  have eq16709 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X0 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq16591 X1 X0
       grind)
    | exact superpose eq16591 eq11
    | (have j1 := eq16591 X1 X0
       grind)
    | exact resolve eq11 eq16591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16591
  have eq16827 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16709 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq16709
    | (have j0 := eq16709 X0 X1
       grind)
    | exact resolve eq16709 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16709
  have eq16878 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16827 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq16827
    | (have j0 := eq16827 (σ X1) (σ X0)
       grind)
    | exact resolve eq16827 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16827
  have eq17049 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16878 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq16878
    | (have j0 := eq16878 X0 X1
       grind)
    | exact resolve eq16878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16878
  have eq17055 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17049 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17049
    | (have j0 := eq17049 X0 X1
       grind)
    | exact resolve eq17049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17049
  have eq17060 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17055 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17055
    | (have j0 := eq17055 X0 X1
       grind)
    | exact resolve eq17055 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17055
  have eq33336 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq289 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq289
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq289 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq50927 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15891 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15891
    | exact resolve eq15891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15891
  have eq51148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50927 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq50927
    | (have j0 := eq50927 X0 X1
       grind)
    | exact resolve eq50927 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50927
  have eq55959 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq16086 X1 (σ X0)
       grind)
    | exact superpose eq16086 eq28
    | (have j1 := eq16086 X1 (σ X0)
       grind)
    | exact resolve eq28 eq16086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16086
  have eq56039 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq55959 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq55959
    | (have j0 := eq55959 X0 X1
       grind)
    | exact resolve eq55959 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55959
  have eq56089 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq56039 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56039
    | (have j0 := eq56039 X0 X1
       grind)
    | exact resolve eq56039 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56039
  have eq56103 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56089 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56089
    | (have j0 := eq56089 X0 X1
       grind)
    | exact resolve eq56089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56089
  have eq64824 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56103 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56103
    | (have j0 := eq56103 X1 (τ X0)
       grind)
    | exact resolve eq56103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64926 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq56103 X0 X1
       grind)
    | exact superpose eq56103 eq11
    | (have j1 := eq56103 X0 X1
       grind)
    | exact resolve eq11 eq56103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56103
  have eq65199 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (M.op X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64824 X0 (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq64824
    | (have j0 := eq64824 X1 (τ X0)
       grind)
    | exact resolve eq64824 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq64824
  have eq65413 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65199 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq65199
    | (have j0 := eq65199 X0 X1
       grind)
    | exact resolve eq65199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65199
  have eq65477 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65413 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq65413
    | (have j0 := eq65413 X0 X1
       grind)
    | exact resolve eq65413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65413
  have eq65824 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65477 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65477
  have eq73291 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64926 x y
       grind)
    | exact superpose eq64926 eq16
    | (have j1 := eq64926 x y
       grind)
    | exact resolve eq16 eq64926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64926
  have eq73973 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq73291
       have i₂ := eq292 y x
       grind)
    | exact superpose eq292 eq73291
    | (have j1 := eq292 y x
       grind)
    | exact resolve eq73291 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73980 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq73291
       have i₂ := eq51148 x y
       grind)
    | exact superpose eq51148 eq73291
    | (have j1 := eq51148 x y
       grind)
    | (have r₁ := eq73291
       have r₂ := eq51148 x y
       grind)
    | exact resolve eq73291 eq51148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51148 eq73291
  have eq73985 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq73980
  have eq73986 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by grind
  clear eq73985
  have eq73993 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq73973
  have eq73994 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq73993
  have eq74001 : y ≠ y ∨ (k x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq73986
       grind)
    | exact superpose eq73986 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq73986
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq73986
       grind)
    | exact resolve eq12 eq73986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73986
  have eq74048 : x = (k x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq74001
  have eq74236 : x ≠ (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq74048
  have eq86804 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17060 y x
       grind)
    | exact superpose eq17060 eq16
    | (have j1 := eq17060 y x
       grind)
    | exact resolve eq16 eq17060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17060
  have eq90398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86804
       have i₂ := eq15613 y x
       grind)
    | exact superpose eq15613 eq86804
    | (have j1 := eq15613 y x
       grind)
    | (have r₁ := eq86804
       have r₂ := eq15613 y x
       grind)
    | exact resolve eq86804 eq15613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15613
  have eq90408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq90398
  have eq90409 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by grind
  clear eq90408
  have eq90421 : x ≠ x ∨ (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq90409
       grind)
    | exact superpose eq90409 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq90409
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq90409
       grind)
    | exact resolve eq12 eq90409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90409
  have eq90472 : (σ x) = (M.op (σ x) (σ y)) ∨ (k y x) = (M.op y y) ∨ y = (k y x) := by grind
  clear eq90421
  have eq90490 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k y x) = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq90472
       grind)
    | exact superpose eq90472 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq90472
       grind)
    | exact resolve eq12 eq90472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90472
  have eq90541 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k y x) = (M.op y y) ∨ y = (k y x) := by grind
  clear eq90490
  have eq90573 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq90541
       have i₂ := eq326 y
       grind)
    | exact superpose eq326 eq90541
    | exact resolve eq90541 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90541
  have eq90600 : y = (k y x) ∨ (k y x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq90573
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq90573
    | exact resolve eq90573 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90573
  have eq90737 : y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ (k y x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq292 x y
       have i₂ := eq90600
       grind)
    | exact superpose eq90600 eq292
    | (have j0 := eq292 x y
       grind)
    | exact resolve eq292 eq90600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90766 : y ≠ (M.op y y) ∨ (k y x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq90600
  have eq90776 : y = (M.op y x) ∨ y = (M.op y y) ∨ (k y x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq90737
  have eq90783 : y = (M.op y x) ∨ (k y x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq90776
       have r₂ := eq90766
       grind)
    | exact resolve eq90776 eq90766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90766 eq90776
  have eq90838 : (τ y) ≠ (τ y) ∨ x = (M.op x y) ∨ (τ y) = (τ (k y x)) ∨ (k y x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq65824 y x
       have i₂ := eq90783
       grind)
    | exact superpose eq90783 eq65824
    | (have j0 := eq65824 y x
       grind)
    | exact resolve eq65824 eq90783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65824 eq90783
  have eq90839 : x = (M.op x y) ∨ (τ y) = (τ (k y x)) ∨ (k y x) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq90838
  have eq90844 : (σ (k y x)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq90839
       have r₂ := eq12 y x
       grind)
    | exact resolve eq90839 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90839
  have eq140465 : (k y x) = (τ (σ (M.op y y))) ∨ (k y x) = (M.op y y) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq90844
       grind)
    | exact superpose eq90844 eq10
    | exact resolve eq10 eq90844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90844
  have eq140559 : (k y x) = (M.op y y) ∨ (k y x) = (M.op y y) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq140465
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq140465
    | exact resolve eq140465 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140465
  have eq140560 : (k y x) = (M.op y y) ∨ (τ y) = (τ (k y x)) := by grind
  clear eq140559
  have eq140565 : (M.op y x) = (M.op y y) ∨ (τ (M.op y x)) = (τ y) ∨ y = (M.op y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq140560
       have i₂ := eq292 x y
       grind)
    | exact superpose eq292 eq140560
    | (have j1 := eq292 x y
       grind)
    | exact resolve eq140560 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140560
  have eq140665 : y = (M.op y x) ∨ (τ (M.op y x)) = (τ y) ∨ (k y x) = (M.op y y) := by
    first
    | (have j1 := eq826 y x
       grind)
    | (have r₁ := eq140565
       have r₂ := eq826 y x
       grind)
    | exact resolve eq140565 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq140565
  have eq140668 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ (τ (M.op y x)) = (τ y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq140665
       grind)
    | exact superpose eq140665 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq140665
       grind)
    | exact resolve eq13 eq140665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140665
  have eq140720 : x = (M.op x y) ∨ y = (k y x) ∨ (τ (M.op y x)) = (τ y) ∨ (k y x) = (M.op y y) := by grind
  clear eq140668
  have eq140723 : (τ (M.op y x)) = (τ y) ∨ y = (k y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq140720
       have r₂ := eq12 y x
       grind)
    | exact resolve eq140720 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140720
  have eq141858 : (M.op y x) = (σ (τ y)) ∨ y = (k y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq11 (M.op y x)
       have i₂ := eq140723
       grind)
    | exact superpose eq140723 eq11
    | exact resolve eq11 eq140723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140723
  have eq142030 : y = (M.op y x) ∨ y = (k y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq141858
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq141858
    | exact resolve eq141858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141858
  have eq142036 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (k y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq142030
       grind)
    | exact superpose eq142030 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq142030
       grind)
    | exact resolve eq13 eq142030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142030
  have eq142088 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ (k y x) = (M.op y y) := by grind
  clear eq142036
  have eq142089 : x = (M.op x y) ∨ y = (k y x) ∨ (k y x) = (M.op y y) := by grind
  clear eq142088
  have eq142111 : y = (k y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq142089
       have r₂ := eq12 y x
       grind)
    | exact resolve eq142089 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142089
  have eq142127 : y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq292 x y
       have i₂ := eq142111
       grind)
    | exact superpose eq142111 eq292
    | (have j0 := eq292 x y
       grind)
    | exact resolve eq292 eq142111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq142159 : y ≠ (M.op y y) ∨ (k y x) = (M.op y y) := by grind
  have eq142172 : y = (M.op y x) ∨ y = (M.op y y) ∨ (k y x) = (M.op y y) := by grind
  clear eq142127
  have eq142182 : y = (M.op y x) ∨ (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq142172
       have r₂ := eq142159
       grind)
    | exact resolve eq142172 eq142159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142172
  have eq142197 : ∀ X0 X1 : G, y ≠ y ∨ (k (M.op (M.op X0 x) X1) y) = (M.op (M.op (M.op X0 x) X1) x) ∨ (k y x) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq75 y x X0 X1
       have i₂ := eq142182
       grind)
    | exact superpose eq142182 eq75
    | (have j0 := eq75 y x X0 X1
       grind)
    | (have r₁ := eq75 y x x x
       have r₂ := eq142182
       grind)
    | exact resolve eq75 eq142182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142244 : ∀ X0 X1 : G, (k y x) = (M.op y y) ∨ (k (M.op (M.op X0 x) X1) y) = (M.op (M.op (M.op X0 x) X1) x) := by
    intro X0 X1
    first
    | (have j0 := eq142197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142197
  have eq148186 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33336 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33336
  have eq148187 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq148186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148186
  have eq148188 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq148187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148187
  have eq148890 : y = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq142111
       have i₂ := eq148188 y x
       grind)
    | exact superpose eq148188 eq142111
    | (have j1 := eq148188 y x
       grind)
    | exact resolve eq142111 eq148188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142111
  have eq148899 : ∀ X0 X1 : G, (M.op y x) = (M.op y y) ∨ (k (M.op (M.op X0 x) X1) y) = (M.op (M.op (M.op X0 x) X1) x) ∨ (M.op y x) = (M.op y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq142244 X0 X1
       have i₂ := eq148188 y x
       grind)
    | exact superpose eq148188 eq142244
    | (have j0 := eq142244 X0 X1
       have j1 := eq148188 y x
       grind)
    | exact resolve eq142244 eq148188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142244 eq148188
  have eq148906 : ∀ X0 X1 : G, (M.op y x) = (M.op y y) ∨ (k (M.op (M.op X0 x) X1) y) = (M.op (M.op (M.op X0 x) X1) x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq148899 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148899
  have eq148915 : y = (M.op y x) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq148890
  have eq149111 : ∀ X0 X1 : G, (k (M.op (M.op X0 x) X1) y) = (M.op (M.op (M.op X0 x) X1) x) ∨ (M.op y x) = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq148906 X0 X1
       have j1 := eq75 y x X0 X1
       grind)
    | (have r₁ := eq148906 X0 X1
       have r₂ := eq75 y x x x
       grind)
    | exact resolve eq148906 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq148906
  have eq155157 : ∀ X0 : G, (k (M.op y X0) y) = (M.op (M.op y X0) x) ∨ y = (M.op y y) ∨ (M.op y x) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq149111 y x
       have i₂ := eq148915
       grind)
    | exact superpose eq148915 eq149111
    | exact resolve eq149111 eq148915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149111
  have eq159961 : (M.op y x) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq155157 x
       have i₂ := eq148915
       grind)
    | exact superpose eq148915 eq155157
    | exact resolve eq155157 eq148915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155157
  have eq160145 : (M.op y x) = (k y y) ∨ y = (M.op y y) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq159961
  have eq160183 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq160145
       have i₂ := eq295 y
       grind)
    | exact superpose eq295 eq160145
    | exact resolve eq160145 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160145
  have eq160184 : y = (M.op y y) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq160183
  have eq160329 : y ≠ (M.op y x) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq160184
  have eq160344 : (M.op y x) = (M.op y y) := by
    first
    | (have r₁ := eq160329
       have r₂ := eq148915
       grind)
    | exact resolve eq160329 eq148915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148915 eq160329
  have eq160364 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq372 y X0 X1
       have i₂ := eq160344
       grind)
    | exact superpose eq160344 eq372
    | exact resolve eq372 eq160344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq160506 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y x) X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 y
       have i₂ := eq160344
       grind)
    | exact superpose eq160344 eq63
    | exact resolve eq63 eq160344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160344
  have eq160562 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq160506 X0 x
       have i₂ := eq63 x x X0 y
       grind)
    | exact superpose eq63 eq160506
    | exact resolve eq160506 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160506
  have eq160725 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (M.op y y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq160562 X0
       grind)
    | exact superpose eq160562 eq12
    | (have j0 := eq12 x X0
       grind)
    | exact resolve eq12 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160913 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq296
       have i₂ := eq160562 x
       grind)
    | exact superpose eq160562 eq296
    | exact resolve eq296 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq160916 : x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq73994
       have i₂ := eq160562 x
       grind)
    | exact superpose eq160562 eq73994
    | exact resolve eq73994 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73994
  have eq160944 : (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq160916
       have r₂ := eq74236
       grind)
    | exact resolve eq160916 eq74236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74236 eq160916
  have eq161024 : ∀ X0 : G, (M.op X0 x) ≠ X0 ∨ (M.op y x) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq160725 X0
       have i₂ := eq160562 y
       grind)
    | exact superpose eq160562 eq160725
    | (have j0 := eq160725 X0
       grind)
    | exact resolve eq160725 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160725
  have eq161292 : y ≠ y ∨ y = (k y y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq161024 y
       have i₂ := eq142182
       grind)
    | exact superpose eq142182 eq161024
    | (have r₁ := eq161024 y
       have r₂ := eq142182
       grind)
    | exact resolve eq161024 eq142182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142182 eq161024
  have eq161301 : y = (k y y) ∨ (k y x) = (M.op y y) := by grind
  clear eq161292
  have eq161332 : y = (M.op y y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq161301
       have i₂ := eq295 y
       grind)
    | exact superpose eq295 eq161301
    | exact resolve eq161301 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq161301
  have eq161350 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq161332
       have r₂ := eq142159
       grind)
    | exact resolve eq161332 eq142159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142159 eq161332
  have eq161368 : (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq161350
       have i₂ := eq160562 y
       grind)
    | exact superpose eq160562 eq161350
    | exact resolve eq161350 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161350
  have eq169471 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq160944
       grind)
    | exact superpose eq160944 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq160944
       grind)
    | exact resolve eq12 eq160944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160944
  have eq169527 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq169471
  have eq169561 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq169527
       have i₂ := eq326 x
       grind)
    | exact superpose eq326 eq169527
    | exact resolve eq169527 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169527
  have eq169601 : (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq169561
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq169561
    | exact resolve eq169561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169561
  have eq170539 : (k x y) = (τ (σ (M.op x x))) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq169601
       grind)
    | exact superpose eq169601 eq10
    | exact resolve eq10 eq169601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169601
  have eq170635 : (k x y) = (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq170539
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq170539
    | exact resolve eq170539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170539
  have eq170636 : (k x y) = (M.op x x) := by grind
  clear eq170635
  have eq170677 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86804
       have i₂ := eq170636
       grind)
    | exact superpose eq170636 eq86804
    | exact resolve eq86804 eq170636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86804
  have eq170685 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq791 y x
       have i₂ := eq170636
       grind)
    | exact superpose eq170636 eq791
    | (have j0 := eq791 y x
       grind)
    | exact resolve eq791 eq170636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq170781 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq170685
       have r₂ := eq160913
       grind)
    | exact resolve eq170685 eq160913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160913 eq170685
  have eq170783 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq170677
       have i₂ := eq160562 x
       grind)
    | exact superpose eq160562 eq170677
    | exact resolve eq170677 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170677
  have eq170784 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq170783
  have eq170792 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq170781
       have i₂ := eq161368
       grind)
    | exact superpose eq161368 eq170781
    | exact resolve eq170781 eq161368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170781
  have eq170794 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq170784
       have i₂ := eq161368
       grind)
    | exact superpose eq161368 eq170784
    | exact resolve eq170784 eq161368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161368 eq170784
  have eq170957 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq170794
       grind)
    | exact superpose eq170794 eq16
    | exact resolve eq16 eq170794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170968 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq170794
       grind)
    | exact superpose eq170794 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq170794
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq170794
       grind)
    | exact resolve eq13 eq170794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170794
  have eq171022 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq170968
  have eq171056 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq171022
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq171022
    | exact resolve eq171022 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171022
  have eq171064 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq170957
       have i₂ := eq160562 x
       grind)
    | exact superpose eq160562 eq170957
    | exact resolve eq170957 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170957
  have eq171097 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq171056
       have i₂ := eq170636
       grind)
    | exact superpose eq170636 eq171056
    | exact resolve eq171056 eq170636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170636 eq171056
  have eq171131 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq171097
       have r₂ := eq171064
       grind)
    | exact resolve eq171097 eq171064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171064 eq171097
  have eq181514 : ∀ X0 X1 : G, (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq170792
       grind)
    | exact superpose eq170792 eq63
    | exact resolve eq63 eq170792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170792
  have eq244666 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op y x)) X1)) ∨ (M.op X2 (σ x)) = (M.op X2 (M.op (σ y) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq181514 X2 X3
       grind)
    | exact superpose eq181514 eq63
    | (have j1 := eq181514 X2 X3
       grind)
    | exact resolve eq63 eq181514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq181514
  have eq244746 : ∀ X0 X2 X3 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X2 (σ x)) = (M.op X2 (M.op (σ y) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq244666 X0 x X2 X3
       have i₂ := eq160364 X0 x
       grind)
    | exact superpose eq160364 eq244666
    | (have j0 := eq244666 X0 x X2 X3
       grind)
    | exact resolve eq244666 eq160364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160364 eq244666
  have eq245148 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq244746 (σ x) X0 X1
       grind)
    | exact superpose eq244746 eq16
    | (have j1 := eq244746 X0 X0 X1
       grind)
    | exact resolve eq16 eq244746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244746
  have eq245242 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245148 X0 X1
       have i₂ := eq326 x
       grind)
    | exact superpose eq326 eq245148
    | (have j0 := eq245148 X0 X1
       grind)
    | exact resolve eq245148 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245148
  have eq245358 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245242 X0 X1
       have i₂ := eq160562 x
       grind)
    | exact superpose eq160562 eq245242
    | (have j0 := eq245242 X0 X1
       grind)
    | exact resolve eq245242 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245242
  have eq245359 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq245358 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245358
  have eq245428 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq245359 X0 (σ y)
       have i₂ := eq326 y
       grind)
    | exact superpose eq326 eq245359
    | exact resolve eq245359 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245446 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq245359 X0 (σ x)
       have i₂ := eq171131
       grind)
    | exact superpose eq171131 eq245359
    | exact resolve eq245359 eq171131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171131 eq245359
  have eq246153 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq245428 X0
       have i₂ := eq160562 y
       grind)
    | exact superpose eq160562 eq245428
    | exact resolve eq245428 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245428
  have eq247317 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ x)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq246153 X0
       have i₂ := eq245446 X1
       grind)
    | exact superpose eq245446 eq246153
    | (have j1 := eq245446 X0
       grind)
    | exact resolve eq246153 eq245446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245446 eq246153
  have eq276300 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq247317 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247317
  have eq276301 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq276300 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276300
  have eq276636 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq276301 (σ x)
       grind)
    | exact superpose eq276301 eq16
    | exact resolve eq16 eq276301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276301
  have eq276752 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq276636
       have i₂ := eq326 x
       grind)
    | exact superpose eq326 eq276636
    | exact resolve eq276636 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq276636
  have eq276980 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq276752
       have i₂ := eq160562 x
       grind)
    | exact superpose eq160562 eq276752
    | exact resolve eq276752 eq160562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160562 eq276752
  have eq276981 : False := by grind
  exact eq276981
