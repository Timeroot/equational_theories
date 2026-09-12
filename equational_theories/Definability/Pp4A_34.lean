import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxx_pyy_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  clear eq35
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq104 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq105 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq107 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq107 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq107 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq108 (σ X0)
       grind)
    | exact superpose eq108 eq10
    | exact resolve eq10 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq43
    | exact resolve eq43 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq113 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq49
    | exact resolve eq49 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq114 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq113
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq113
    | exact resolve eq113 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq111
    | exact resolve eq111 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq110
    | exact resolve eq110 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq110
  have eq746 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq117 X1
       grind)
    | exact superpose eq117 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq747 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq746 X0 X1
       have i₂ := eq117 X1
       grind)
    | exact superpose eq117 eq746
    | (have j0 := eq746 X0 X1
       grind)
    | exact resolve eq746 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq746
  have eq861 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq747 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq49303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq49303
    | exact resolve eq49303 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49303
  have eq49315 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq49304
       have r₂ := eq27
       grind)
    | exact resolve eq49304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49304
  have eq49319 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq49315
    | exact resolve eq49315 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49315
  have eq49321 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49319 eq105
    | (have r₁ := eq105
       have r₂ := eq49319
       grind)
    | exact resolve eq105 eq49319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq49394 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq49319
  have eq49396 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq49321
  have eq50748 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq49396
       have r₂ := eq49394
       grind)
    | exact resolve eq49396 eq49394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49394 eq49396
  have eq51060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq50748 eq92
    | exact resolve eq92 eq50748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq50748
  have eq51073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq51060
  have eq51076 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq51073
       have r₂ := eq27
       grind)
    | exact resolve eq51073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51073
  have eq51079 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51076 eq114
    | exact resolve eq114 eq51076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51076
  have eq51181 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq51079
    | exact resolve eq51079 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51079
  have eq51182 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq51181
  have eq51193 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq51182
       grind)
    | exact superpose eq51182 eq104
    | (have r₁ := eq104
       have r₂ := eq51182
       grind)
    | exact resolve eq104 eq51182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq51194 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq51182
       grind)
    | exact superpose eq51182 eq116
    | exact resolve eq116 eq51182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51268 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq51182
  have eq51270 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq51193
  have eq51291 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq51194
    | exact resolve eq51194 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51194
  have eq52589 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq51270
       have r₂ := eq51268
       grind)
    | exact resolve eq51270 eq51268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51268 eq51270
  have eq52603 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq861 x y
       have i₂ := eq52589
       grind)
    | exact superpose eq52589 eq861
    | (have j0 := eq861 x y
       grind)
    | exact resolve eq861 eq52589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq52589
  have eq52607 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52603
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq52603
    | exact resolve eq52603 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52603
  have eq52620 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq52607
    | exact resolve eq52607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52607
  have eq52626 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq52620
       have r₂ := eq51291
       grind)
    | exact resolve eq52620 eq51291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52620
  have eq52630 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52626
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq52626
    | exact resolve eq52626 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52626
  have eq52634 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52630
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52630
    | exact resolve eq52630 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52630
  have eq52638 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52634
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52634
    | exact resolve eq52634 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52634
  have eq52642 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq52638
    | exact resolve eq52638 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52638
  have eq52646 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52642
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq52642
    | exact resolve eq52642 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52642
  have eq52650 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52646
    | exact resolve eq52646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52646
  have eq68457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq52650 eq51291
    | exact resolve eq51291 eq52650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51291 eq52650
  have eq68537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq68457
  have eq68555 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq68537
       have r₂ := eq27
       grind)
    | exact resolve eq68537 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68537
  have eq68826 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq68555 eq114
    | exact resolve eq114 eq68555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq68555
  have eq68963 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq68826
    | exact resolve eq68826 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq68826
  have eq68964 : x = (M.op x x) := by grind
  clear eq68963
  have eq68978 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq68964
       grind)
    | exact superpose eq68964 eq116
    | exact resolve eq116 eq68964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq68988 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq68964
       grind)
    | exact superpose eq68964 eq52
    | exact resolve eq52 eq68964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69108 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68988 X0
       have i₂ := eq68964
       grind)
    | exact superpose eq68964 eq68988
    | exact resolve eq68988 eq68964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68964 eq68988
  have eq69117 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68978
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq68978
    | exact resolve eq68978 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq68978
  have eq69152 : y = (M.op x y) := by
    first
    | (have i₁ := eq69108 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq69108
    | (have j0 := eq69108 y
       grind)
    | exact resolve eq69108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq69108
  have eq69396 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq69152 eq20
    | exact resolve eq20 eq69152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq69152
  have eq69562 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq69396
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq69396
    | exact resolve eq69396 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq69396
  have eq69794 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq69117 eq52
    | exact resolve eq52 eq69117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq69915 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq69117 eq69794
    | exact resolve eq69794 eq69117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69117 eq69794
  have eq69995 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69915 eq26
    | (have j1 := eq69915 (σ y)
       grind)
    | exact resolve eq26 eq69915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq69915
  have eq70196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69562 eq69995
    | exact resolve eq69995 eq69562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69562 eq69995
  have eq70229 : False := by grind
  exact eq70229

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyy_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  clear eq35
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq104 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq105 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq107 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq107 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq107 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq110 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq108 (σ X0)
       grind)
    | exact superpose eq108 eq10
    | exact resolve eq10 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq43
    | exact resolve eq43 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq113 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq49
    | exact resolve eq49 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq114 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq113
       have i₂ := eq108 x
       grind)
    | exact superpose eq108 eq113
    | exact resolve eq113 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq108 sF2
       grind)
    | exact superpose eq108 eq111
    | exact resolve eq111 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq110
    | exact resolve eq110 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq110
  have eq725 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq117 X1
       grind)
    | exact superpose eq117 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq726 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 X1
       have i₂ := eq117 X1
       grind)
    | exact superpose eq117 eq725
    | (have j0 := eq725 X0 X1
       grind)
    | exact resolve eq725 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq725
  have eq836 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq726 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq30198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq30198
    | exact resolve eq30198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30198
  have eq30210 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq30199
       have r₂ := eq27
       grind)
    | exact resolve eq30199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30199
  have eq30214 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq30210
    | exact resolve eq30210 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30210
  have eq30216 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30214 eq105
    | (have r₁ := eq105
       have r₂ := eq30214
       grind)
    | exact resolve eq105 eq30214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq30266 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq30214
  have eq30268 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq30216
  have eq31183 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq30268
       have r₂ := eq30266
       grind)
    | exact resolve eq30268 eq30266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30266 eq30268
  have eq31189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31183 eq92
    | exact resolve eq92 eq31183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq31183
  have eq31202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31189
  have eq31205 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq31202
       have r₂ := eq27
       grind)
    | exact resolve eq31202 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31202
  have eq31208 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31205 eq114
    | exact resolve eq114 eq31205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31205
  have eq31280 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq31208
    | exact resolve eq31208 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31208
  have eq31281 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq31280
  have eq31294 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq31281
       grind)
    | exact superpose eq31281 eq104
    | (have r₁ := eq104
       have r₂ := eq31281
       grind)
    | exact resolve eq104 eq31281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq31295 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq31281
       grind)
    | exact superpose eq31281 eq116
    | exact resolve eq116 eq31281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31344 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq31281
  have eq31346 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq31294
  have eq31364 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq31295
    | exact resolve eq31295 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31295
  have eq31989 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq31346
       have r₂ := eq31344
       grind)
    | exact resolve eq31346 eq31344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31344 eq31346
  have eq32003 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq836 x y
       have i₂ := eq31989
       grind)
    | exact superpose eq31989 eq836
    | (have j0 := eq836 x y
       grind)
    | exact resolve eq836 eq31989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq31989
  have eq32007 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32003
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq32003
    | exact resolve eq32003 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32003
  have eq32020 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq32007
    | exact resolve eq32007 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32007
  have eq32026 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq32020
       have r₂ := eq31364
       grind)
    | exact resolve eq32020 eq31364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32020
  have eq32030 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32026
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq32026
    | exact resolve eq32026 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32026
  have eq32034 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32030
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32030
    | exact resolve eq32030 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32030
  have eq32038 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32034
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32034
    | exact resolve eq32034 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32034
  have eq32042 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq32038
    | exact resolve eq32038 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32038
  have eq32046 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32042
       have i₂ := eq116
       grind)
    | exact superpose eq116 eq32042
    | exact resolve eq32042 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32042
  have eq32050 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32046
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32046
    | exact resolve eq32046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32046
  have eq39145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32050 eq31364
    | exact resolve eq31364 eq32050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31364 eq32050
  have eq39193 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq39145
  have eq39209 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq39193
       have r₂ := eq27
       grind)
    | exact resolve eq39193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39193
  have eq39686 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39209 eq114
    | exact resolve eq114 eq39209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq39209
  have eq39778 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq39686
    | exact resolve eq39686 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39686
  have eq39779 : x = (M.op x x) := by grind
  clear eq39778
  have eq39793 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq39779
       grind)
    | exact superpose eq39779 eq116
    | exact resolve eq116 eq39779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq39804 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq39779
       grind)
    | exact superpose eq39779 eq52
    | exact resolve eq52 eq39779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39871 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39804 X0
       have i₂ := eq39779
       grind)
    | exact superpose eq39779 eq39804
    | exact resolve eq39804 eq39779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39779 eq39804
  have eq39881 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq39793
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39793
    | exact resolve eq39793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39793
  have eq39904 : y = (M.op x y) := by
    first
    | (have i₁ := eq39871 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39871
    | (have j0 := eq39871 y
       grind)
    | exact resolve eq39871 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq39871
  have eq40372 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq39904 eq20
    | exact resolve eq20 eq39904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq39904
  have eq40538 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40372
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40372
    | exact resolve eq40372 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq40372
  have eq40765 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq39881 eq52
    | exact resolve eq52 eq39881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq40831 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq39881 eq40765
    | exact resolve eq40765 eq39881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39881 eq40765
  have eq41435 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40831 eq26
    | (have j1 := eq40831 (σ y)
       grind)
    | exact resolve eq26 eq40831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40831
  have eq41558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40538 eq41435
    | exact resolve eq41435 eq40538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40538 eq41435
  have eq41584 : False := by grind
  exact eq41584

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq19 eq33
    | exact resolve eq33 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq35 X1 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq40 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq61
    | exact resolve eq61 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq61
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq112 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq63
    | exact resolve eq63 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq13
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq19
    | exact resolve eq19 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op X1 X1) X1))
       have i₂ := eq40 (τ X0) X1
       grind)
    | exact superpose eq40 eq17
    | exact resolve eq17 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq163 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op X1 X1) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq157
    | exact resolve eq157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq252 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq90
    | exact resolve eq90 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | (have j0 := eq90 X1 X1
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq275 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq255
    | (have j0 := eq255 X0 X1
       grind)
    | exact resolve eq255 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq278 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq252 X0 X1 X2
       have i₂ := eq112 X0 X1
       grind)
    | exact superpose eq112 eq252
    | (have j0 := eq252 X0 X1 X2
       grind)
    | exact resolve eq252 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq281 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       have j1 := eq118 X1 X0
       grind)
    | (have r₁ := eq275 X0 X0
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq275 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq275
  have eq284 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq278 X0 X1 X2
       have i₂ := eq112 X0 X1
       grind)
    | exact superpose eq112 eq278
    | (have j0 := eq278 X0 X1 X2
       grind)
    | exact resolve eq278 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq278
  have eq373 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq119
    | exact resolve eq119 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq417 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq63 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq63 eq373
    | exact resolve eq373 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq424 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq417 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq417 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq417
    | exact resolve eq417 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq432 : ∀ X0 X1 : G, (M.op (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq424 (σ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq424 X0 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq424 eq424
    | exact resolve eq424 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq464 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq63 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq63 eq432
    | exact resolve eq432 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq475 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq464 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq464
    | exact resolve eq464 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq523 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op (M.op X1 X1) X1)))
       have i₂ := eq163 (τ X0) X1
       grind)
    | exact superpose eq163 eq17
    | exact resolve eq17 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (M.op X1 X1) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq523
    | exact resolve eq523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq875 : ∀ X0 X1 : G, (M.op (σ (σ (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq475 (σ (σ (M.op (M.op X0 X0) X0))) X1
       have i₂ := eq475 X0 (σ (σ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq475 eq475
    | exact resolve eq475 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq163 X1 (σ (σ (M.op (M.op X0 X0) X0)))
       have i₂ := eq475 X0 (σ (σ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq475 eq163
    | exact resolve eq163 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq911 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq899 X0 X1
       have i₂ := eq63 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq63 eq899
    | exact resolve eq899 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq923 : ∀ X0 X1 : G, (M.op (σ (σ (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq875 X0 X1
       have i₂ := eq63 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq63 eq875
    | exact resolve eq875 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq935 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq911 X0 X1
       have i₂ := eq63 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq63 eq911
    | exact resolve eq911 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq943 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq923 X0 X1
       have i₂ := eq63 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq63 eq923
    | exact resolve eq923 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq950 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq935 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq935 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq935
    | exact resolve eq935 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq957 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq943 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq943 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq943
    | exact resolve eq943 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq1657 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq281
    | exact resolve eq281 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1677 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq281 (σ X1) X0
       grind)
    | exact superpose eq281 eq15
    | (have j1 := eq281 (σ X1) X0
       grind)
    | exact resolve eq15 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq1690 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1657 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq1657
    | (have j0 := eq1657 X0 X1
       grind)
    | exact resolve eq1657 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1657
  have eq2227 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq529 X1 (σ (σ (M.op (M.op X0 X0) X0)))
       have i₂ := eq475 X0 (σ (σ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq475 eq529
    | exact resolve eq529 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq529
  have eq2264 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2227 X0 X1
       have i₂ := eq63 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq63 eq2227
    | exact resolve eq2227 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2280 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2264 X0 X1
       have i₂ := eq63 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq63 eq2264
    | exact resolve eq2264 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq2285 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2280 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq2280 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq2280
    | exact resolve eq2280 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq7939 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq950 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1
       have i₂ := eq957 X0 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       grind)
    | exact superpose eq957 eq950
    | exact resolve eq950 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq7991 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op (σ (σ (σ (M.op (M.op X0 X0) X0)))) (σ (σ (σ (M.op (M.op X0 X0) X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7939 X0 X1
       have i₂ := eq63 (σ (σ (σ (M.op (M.op X0 X0) X0))))
       grind)
    | exact superpose eq63 eq7939
    | exact resolve eq7939 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7939
  have eq8061 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7991 X0 X1
       have i₂ := eq63 (σ (σ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq63 eq7991
    | exact resolve eq7991 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991
  have eq8120 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8061 X0 X1
       have i₂ := eq63 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq63 eq8061
    | exact resolve eq8061 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061
  have eq8171 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8120 X0 X1
       have i₂ := eq63 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq63 eq8120
    | exact resolve eq8120 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8120
  have eq8215 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8171 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq8171 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq8171
    | exact resolve eq8171 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171
  have eq10767 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq284 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq11763 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1690 X0 (τ X1)
       grind)
    | exact superpose eq1690 eq17
    | (have j1 := eq1690 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1690
  have eq17998 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2285 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1
       have i₂ := eq957 X0 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       grind)
    | exact superpose eq957 eq2285
    | exact resolve eq2285 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq2285
  have eq18088 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (M.op (σ (σ (σ (M.op (M.op X0 X0) X0)))) (σ (σ (σ (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17998 X0 X1
       have i₂ := eq63 (σ (σ (σ (M.op (M.op X0 X0) X0))))
       grind)
    | exact superpose eq63 eq17998
    | exact resolve eq17998 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17998
  have eq18138 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18088 X0 X1
       have i₂ := eq63 (σ (σ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq63 eq18088
    | exact resolve eq18088 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18088
  have eq18162 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18138 X0 X1
       have i₂ := eq63 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq63 eq18138
    | exact resolve eq18138 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18138
  have eq18176 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18162 X0 X1
       have i₂ := eq63 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq63 eq18162
    | exact resolve eq18162 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq18162
  have eq18183 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18176 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq18176 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq18176
    | exact resolve eq18176 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq18176
  have eq37452 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1677 x y
       grind)
    | exact superpose eq1677 eq16
    | (have j1 := eq1677 x y
       grind)
    | exact resolve eq16 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37587 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq174722 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11763 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11763
    | exact resolve eq11763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11763
  have eq175211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq174722 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq174722
    | (have j0 := eq174722 X0 X1
       grind)
    | exact resolve eq174722 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174722
  have eq291073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq37452
       have i₂ := eq175211 y x
       grind)
    | exact superpose eq175211 eq37452
    | (have j1 := eq175211 y x
       grind)
    | (have r₁ := eq37452
       have r₂ := eq175211 y x
       grind)
    | exact resolve eq37452 eq175211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37452
  have eq291076 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq291073
  have eq291800 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq291076
       grind)
    | exact superpose eq291076 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq291076
       grind)
    | exact resolve eq13 eq291076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291835 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq291800
  have eq298658 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10767 X1 (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))))) X2
       have i₂ := eq18183 X0 X1
       grind)
    | exact superpose eq18183 eq10767
    | exact resolve eq10767 eq18183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10767 eq18183
  have eq298768 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (σ (k X2 (τ X0))) ∨ (M.op X0 (σ X2)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq298658 X0 x X2
       have i₂ := eq8215 x (τ X0)
       grind)
    | exact superpose eq8215 eq298658
    | (have j0 := eq298658 X0 x X2
       grind)
    | exact resolve eq298658 eq8215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8215 eq298658
  have eq298869 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (M.op X0 (σ X2)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq298768 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq298768
    | (have j0 := eq298768 X0 X2
       grind)
    | exact resolve eq298768 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq298768
  have eq298934 : ∀ X0 X2 : G, (M.op X0 (σ X2)) ≠ X0 ∨ (M.op X0 (σ X2)) = (k (σ X2) X0) := by
    intro X0 X2
    first
    | (have j0 := eq298869 X0 X2
       have j1 := eq12 (σ X2) X0
       grind)
    | (have r₁ := eq298869 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq298869 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298869
  have eq299026 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq298934 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq298934
    | exact resolve eq298934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298934
  have eq299366 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq299026 y x
       have i₂ := eq291076
       grind)
    | exact superpose eq291076 eq299026
    | (have j0 := eq299026 x x
       grind)
    | exact resolve eq299026 eq291076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291076
  have eq299369 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq299366
       have r₂ := eq291835
       grind)
    | exact resolve eq299366 eq291835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291835 eq299366
  have eq300486 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq37587 x y
       have i₂ := eq299369
       grind)
    | exact superpose eq299369 eq37587
    | (have j0 := eq37587 x y
       grind)
    | exact resolve eq37587 eq299369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37587 eq299369
  have eq300490 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq300486
  have eq300491 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq300490
  have eq300508 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq300491
       grind)
    | exact superpose eq300491 eq16
    | exact resolve eq16 eq300491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300509 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq116 x (σ y)
       have i₂ := eq300491
       grind)
    | exact superpose eq300491 eq116
    | (have j0 := eq116 x (σ y)
       grind)
    | (have r₁ := eq116 x (σ y)
       have r₂ := eq300491
       grind)
    | exact resolve eq116 eq300491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq300553 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq299026 (σ y) (σ x)
       have i₂ := eq300491
       grind)
    | exact superpose eq300491 eq299026
    | exact resolve eq299026 eq300491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299026 eq300491
  have eq300554 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq300509
  have eq300555 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq300553
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq300553
    | exact resolve eq300553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300553
  have eq300558 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq300554
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq300554
    | exact resolve eq300554 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300554
  have eq300560 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq300558
       have r₂ := eq300555
       grind)
    | exact resolve eq300558 eq300555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300555 eq300558
  have eq301113 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq175211 y x
       have i₂ := eq300560
       grind)
    | exact superpose eq300560 eq175211
    | (have j0 := eq175211 y x
       grind)
    | exact resolve eq175211 eq300560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175211 eq300560
  have eq301318 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq301113
       have r₂ := eq300508
       grind)
    | exact resolve eq301113 eq300508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301113
  have eq302155 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq300508
       have i₂ := eq301318
       grind)
    | exact superpose eq301318 eq300508
    | exact resolve eq300508 eq301318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300508 eq301318
  have eq302195 : False := by grind
  exact eq302195

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_y_pyy_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq86 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq53 (σ X0)
       grind)
    | exact superpose eq53 eq15
    | (have j1 := eq53 (σ X0)
       grind)
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) (σ X0)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq78 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq269 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq256 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq270 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq273 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq278 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       have j1 := eq266 X0 X1
       grind)
    | (have r₁ := eq273 X0 X1
       have r₂ := eq266 X0 X1
       grind)
    | (have r₁ := eq273 X0 X0
       have r₂ := eq266 X0 X0
       grind)
    | exact resolve eq273 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq273
  have eq494 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq676 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq494 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq494
    | (have j0 := eq494 (τ X0)
       grind)
    | exact resolve eq494 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq676 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq676
    | (have j0 := eq676 X0
       grind)
    | exact resolve eq676 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq686 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq682 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq682
    | (have j0 := eq682 X0
       grind)
    | exact resolve eq682 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq690 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq278 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq278 x y
       grind)
    | exact superpose eq278 eq16
    | (have j1 := eq278 x x
       grind)
    | exact resolve eq16 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq720 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq690
    | (have j0 := eq690 X0 X1
       grind)
    | exact resolve eq690 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq690
  have eq727 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq686 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq686
    | (have j0 := eq686 (τ X0)
       grind)
    | exact resolve eq686 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq686
  have eq733 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq720
    | (have j0 := eq720 X1 X1
       grind)
    | exact resolve eq720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq869 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq733 (τ X1) X0
       grind)
    | exact superpose eq733 eq17
    | (have j1 := eq733 X0 X0
       grind)
    | exact resolve eq17 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq733
  have eq1045 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq869 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq869
    | (have j0 := eq869 X1 X1
       grind)
    | exact resolve eq869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq1097 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1045 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1045
    | (have j0 := eq1045 X0 X1
       grind)
    | exact resolve eq1045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq702
       have i₂ := eq1097 y x
       grind)
    | exact superpose eq1097 eq702
    | (have j1 := eq1097 x (σ x)
       grind)
    | (have r₁ := eq702
       have r₂ := eq1097 y x
       grind)
    | exact resolve eq702 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq1097
  have eq1185 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1184
  have eq1188 : ∀ X0 : G, x ≠ x ∨ x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1185
       grind)
    | exact superpose eq1185 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1185
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1185
       grind)
    | exact resolve eq12 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1198 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1188 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1205 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ x = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq1198 X1
       grind)
    | exact superpose eq1198 eq12
    | (have j0 := eq12 X0 (σ x)
       have j1 := eq1198 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1198 X0
       grind)
    | exact resolve eq12 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1215 : ∀ X0 X1 : G, x = (k X1 x) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0 X1
    first
    | (have j0 := eq1205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1224 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq494 x
       have i₂ := eq1215 X0 x
       grind)
    | exact superpose eq1215 eq494
    | (have j0 := eq494 x
       have j1 := eq1215 X0 x
       grind)
    | exact resolve eq494 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq1215
  have eq1242 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq1224 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1247 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq1242 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq1242 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq1242 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1301 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq727 (σ x)
       have i₂ := eq1247 (σ x)
       grind)
    | exact superpose eq1247 eq727
    | (have j0 := eq727 (σ x)
       grind)
    | exact resolve eq727 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1305 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq53 (σ x)
       have i₂ := eq1247 (σ x)
       grind)
    | exact superpose eq1247 eq53
    | (have j0 := eq53 (σ x)
       grind)
    | exact resolve eq53 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1247
  have eq1323 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1305
  have eq1326 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by grind
  clear eq1301
  have eq1336 : x = (M.op x x) := by
    first
    | (have i₁ := eq1326
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1326
    | exact resolve eq1326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1407 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 x X0
       have i₂ := eq1336
       grind)
    | exact superpose eq1336 eq31
    | exact resolve eq31 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1407 X0
       have i₂ := eq1336
       grind)
    | exact superpose eq1336 eq1407
    | exact resolve eq1407 eq1336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336 eq1407
  have eq1650 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 (σ x) X0
       have i₂ := eq1323
       grind)
    | exact superpose eq1323 eq31
    | exact resolve eq31 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1666 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1650 X0
       have i₂ := eq1323
       grind)
    | exact superpose eq1323 eq1650
    | exact resolve eq1650 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323 eq1650
  have eq1672 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1666 (σ y)
       grind)
    | exact superpose eq1666 eq16
    | exact resolve eq16 eq1666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq1708 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1672
       have i₂ := eq1421 y
       grind)
    | exact superpose eq1421 eq1672
    | exact resolve eq1672 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421 eq1672
  have eq1709 : False := by grind
  exact eq1709

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxx_x_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq176 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq1021 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1031 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1097 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1030
       grind)
    | exact superpose eq1030 eq39
    | exact resolve eq39 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1097
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1097
    | exact resolve eq1097 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1098
    | exact resolve eq1098 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1100 eq1031
    | exact resolve eq1031 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1115 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1108
       have r₂ := eq27
       grind)
    | exact resolve eq1108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1123 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1115 eq176
    | exact resolve eq176 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 : G, x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1115 eq1123
    | exact resolve eq1123 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq1123
  have eq1133 : ∀ X0 X1 : G, (M.op (M.op x x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq1128 X1
       grind)
    | exact superpose eq1128 eq176
    | (have j1 := eq1128 (σ y)
       grind)
    | exact resolve eq176 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1138 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1128 eq1133
    | (have j0 := eq1133 X0 X1
       have j1 := eq1128 X1
       grind)
    | exact resolve eq1133 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq1133
  have eq1141 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq1138 (M.op sF2 sF3) x
       grind)
    | exact superpose eq1138 eq26
    | (have j1 := eq1138 y (σ y)
       grind)
    | exact resolve eq26 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1152 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1159 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1152 y
       grind)
    | exact superpose eq1152 eq18
    | (have j1 := eq1152 y
       grind)
    | exact resolve eq18 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1170 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1159
  have eq1175 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1170 eq1021
    | (have r₁ := eq1021
       have r₂ := eq1170
       grind)
    | exact resolve eq1021 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq1170
  have eq1179 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1175
  have eq1228 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1179 eq141
    | exact resolve eq141 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1233 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1228
    | exact resolve eq1228 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1228
  have eq1243 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1233 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1233
       grind)
    | exact resolve eq13 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1248 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1243 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1415 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1233
       have i₂ := eq1248 sF2
       grind)
    | exact superpose eq1248 eq1233
    | exact resolve eq1233 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233 eq1248
  have eq1422 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq1415
  have eq1471 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1422 eq141
    | exact resolve eq141 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1422
  have eq1476 : y = (k y x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1471
    | exact resolve eq1471 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1471
  have eq1480 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1030
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq1030
    | exact resolve eq1030 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq1476
  have eq1483 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq1480
  have eq1487 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1064 x
       grind)
    | (have r₁ := eq1483
       have r₂ := eq1064 x
       grind)
    | exact resolve eq1483 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq1483
  have eq1495 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq1487
       grind)
    | exact superpose eq1487 eq176
    | exact resolve eq176 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1509 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1487 eq1495
    | exact resolve eq1495 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487 eq1495
  have eq1514 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1509 y
       grind)
    | exact superpose eq1509 eq18
    | (have j1 := eq1509 y
       grind)
    | exact resolve eq18 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1509
  have eq1531 : y = (M.op x y) := by grind
  clear eq1514
  have eq1539 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1531
       grind)
    | exact superpose eq1531 eq24
    | exact resolve eq24 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1544 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq1020
       have i₂ := eq1531
       grind)
    | exact superpose eq1531 eq1020
    | (have r₁ := eq1020
       have r₂ := eq1531
       grind)
    | exact resolve eq1020 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq1531
  have eq1545 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x x) := by grind
  clear eq1544
  have eq1547 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1539 eq20
    | exact resolve eq20 eq1539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539
  have eq2208 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1545 eq39
    | exact resolve eq39 eq1545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq2212 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2208
    | exact resolve eq2208 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2208
  have eq2215 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1547 eq2212
    | exact resolve eq2212 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq2224 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2215 eq1031
    | exact resolve eq1031 eq2215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq2215
  have eq2231 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq2224
  have eq2350 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2231 eq176
    | exact resolve eq176 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2363 : ∀ X0 : G, x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2231 eq2350
    | exact resolve eq2350 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231 eq2350
  have eq2371 : ∀ X0 X1 : G, (M.op (M.op x x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq2363 X1
       grind)
    | exact superpose eq2363 eq176
    | (have j1 := eq2363 (σ y)
       grind)
    | exact resolve eq176 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2385 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2363 eq2371
    | (have j0 := eq2371 X0 X1
       have j1 := eq2363 X1
       grind)
    | exact resolve eq2371 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363 eq2371
  have eq2391 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq2385 (M.op sF2 sF3) x
       grind)
    | exact superpose eq2385 eq26
    | (have j1 := eq2385 X0 (σ y)
       grind)
    | exact resolve eq26 eq2385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385
  have eq2412 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2391 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2424 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2412 x
       grind)
    | exact superpose eq2412 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq2412 x
       grind)
    | exact resolve eq13 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2443 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2424 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2502 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2412 x
       have i₂ := eq2443 x
       grind)
    | exact superpose eq2443 eq2412
    | exact resolve eq2412 eq2443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412
  have eq2517 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2502
  have eq2550 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq2517
       grind)
    | exact superpose eq2517 eq39
    | exact resolve eq39 eq2517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2517
  have eq2558 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2550
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2550
    | exact resolve eq2550 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2550
  have eq2565 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2558 eq1062
    | (have j0 := eq1062 (σ x) (σ x)
       grind)
    | (have r₁ := eq1062 (σ x) (σ x)
       have r₂ := eq2558
       grind)
    | exact resolve eq1062 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq2558
  have eq2566 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2565
  have eq2567 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2566
  have eq2579 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2567 eq176
    | exact resolve eq176 eq2567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2584 : (σ x) = (k (σ x) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2567 eq2443
    | exact resolve eq2443 eq2567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567
  have eq2588 : (σ x) = (k (σ x) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2584
  have eq2595 : ∀ X0 : G, (M.op (k (σ x) x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2443 eq2579
    | exact resolve eq2579 eq2443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2443 eq2579
  have eq2597 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2588 eq2595
    | exact resolve eq2595 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588 eq2595
  have eq2610 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2597 eq26
    | (have j1 := eq2597 (σ y)
       grind)
    | exact resolve eq26 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2597
  have eq2633 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2610
  have eq2644 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2633 eq27
    | exact resolve eq27 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2633
  have eq2646 : False := by grind
  exact eq2646

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyy_x_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
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
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq81 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq82 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq43
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq43 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq88 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X0)) = (k X1 (τ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq33 X0 (σ X1)
       grind)
    | exact superpose eq33 eq40
    | exact resolve eq40 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq40
  have eq254 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq264 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq279 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq264 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq264
    | (have j0 := eq264 (τ X0)
       grind)
    | exact resolve eq264 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq264
  have eq283 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq279
    | (have j0 := eq279 X0
       grind)
    | exact resolve eq279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq286 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq283
    | (have j0 := eq283 X0
       grind)
    | exact resolve eq283 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq517 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) ≠ (τ (M.op (M.op X0 X0) X0)) ∨ (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq286 (τ (M.op (M.op X0 X0) X0))
       have i₂ := eq88 X0 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq88 eq286
    | (have j0 := eq286 (τ (M.op (M.op X0 X0) X0))
       grind)
    | (have r₁ := eq286 (τ (M.op (M.op X0 X0) X0))
       have r₂ := eq88 X0 (τ (M.op (M.op X0 X0) X0))
       grind)
    | exact resolve eq286 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq286
  have eq530 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have j0 := eq517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq678 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq81
    | (have j0 := eq81 X1 X1
       grind)
    | exact resolve eq81 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq714 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq678
    | (have j0 := eq678 X0 X1
       grind)
    | exact resolve eq678 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq1022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq254
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq254
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq254 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1023 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1022
  have eq7615 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1023
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1023
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1023
       grind)
    | exact resolve eq13 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq7633 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7615
  have eq7634 : y = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7633
  have eq10893 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq530 X0
       grind)
    | exact superpose eq530 eq19
    | exact resolve eq19 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10967 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10893 X0 X1
       have i₂ := eq530 X0
       grind)
    | exact superpose eq530 eq10893
    | exact resolve eq10893 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq10893
  have eq276821 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq82 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq276823 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq276821 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276821
  have eq276830 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq276823 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq276823
    | exact resolve eq276823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276823
  have eq277021 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq276830 X0
       have i₂ := eq30 (σ X0) X0
       grind)
    | exact superpose eq30 eq276830
    | (have j0 := eq276830 X0
       grind)
    | exact resolve eq276830 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq276830
  have eq277024 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq277021 X0
       have j1 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq277021 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq277021 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277021
  have eq277027 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq277024 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277024
    | exact resolve eq277024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277024
  have eq277301 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq262 X0 X0
       have i₂ := eq277027 X0
       grind)
    | exact superpose eq277027 eq262
    | (have j0 := eq262 X0 X0
       grind)
    | exact resolve eq262 eq277027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277542 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq277027 (σ X0)
       grind)
    | exact superpose eq277027 eq15
    | exact resolve eq15 eq277027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277662 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq277301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277301
  have eq277753 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq277542 X0
       have i₂ := eq277027 X0
       grind)
    | exact superpose eq277027 eq277542
    | exact resolve eq277542 eq277027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277027 eq277542
  have eq279924 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X1
       have i₂ := eq277753 X0
       grind)
    | exact superpose eq277753 eq19
    | exact resolve eq19 eq277753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq279982 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10967 (σ X0) X1
       have i₂ := eq277753 X0
       grind)
    | exact superpose eq277753 eq10967
    | exact resolve eq10967 eq277753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10967
  have eq280509 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq262 x y
       have i₂ := eq7634
       grind)
    | exact superpose eq7634 eq262
    | (have j0 := eq262 x y
       grind)
    | exact resolve eq262 eq7634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq7634
  have eq280575 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq280509
  have eq280576 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq280575
  have eq280584 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq280576
       have i₂ := eq277753 x
       grind)
    | exact superpose eq277753 eq280576
    | exact resolve eq280576 eq277753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280576
  have eq862760 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq280584
       grind)
    | exact superpose eq280584 eq16
    | exact resolve eq16 eq280584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862762 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq280584
       grind)
    | exact superpose eq280584 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq280584
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq280584
       grind)
    | exact resolve eq13 eq280584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280584
  have eq862816 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq862762
  have eq862817 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq277662 x
       grind)
    | (have r₁ := eq862816
       have r₂ := eq277662 x
       grind)
    | exact resolve eq862816 eq277662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862816
  have eq862818 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq862817
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq862817
    | exact resolve eq862817 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862817
  have eq862819 : x = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq862818
       have i₂ := eq277753 x
       grind)
    | exact superpose eq277753 eq862818
    | exact resolve eq862818 eq277753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862818
  have eq865119 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq277662 x
       have i₂ := eq862819
       grind)
    | exact superpose eq862819 eq277662
    | (have j0 := eq277662 x
       grind)
    | (have r₁ := eq277662 x
       have r₂ := eq862819
       grind)
    | exact resolve eq277662 eq862819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862819
  have eq865306 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq865119
  have eq865405 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j1 := eq277662 x
       grind)
    | (have r₁ := eq865306
       have r₂ := eq277662 x
       grind)
    | exact resolve eq865306 eq277662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865306
  have eq865495 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq865405
       have i₂ := eq277753 x
       grind)
    | exact superpose eq277753 eq865405
    | exact resolve eq865405 eq277753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865405
  have eq865580 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq714 y x
       have i₂ := eq865495
       grind)
    | exact superpose eq865495 eq714
    | (have j0 := eq714 y x
       grind)
    | exact resolve eq714 eq865495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq865495
  have eq866252 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq865580
       have r₂ := eq862760
       grind)
    | exact resolve eq865580 eq862760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865580
  have eq871050 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq862760
       have i₂ := eq866252
       grind)
    | exact superpose eq866252 eq862760
    | exact resolve eq862760 eq866252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862760 eq866252
  have eq871108 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq871050
  have eq871109 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq871108
  have eq873476 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq277662 x
       have i₂ := eq871109
       grind)
    | exact superpose eq871109 eq277662
    | (have j0 := eq277662 x
       grind)
    | (have r₁ := eq277662 x
       have r₂ := eq871109
       grind)
    | exact resolve eq277662 eq871109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871109
  have eq873663 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq873476
  have eq873762 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq277662 x
       grind)
    | (have r₁ := eq873663
       have r₂ := eq277662 x
       grind)
    | exact resolve eq873663 eq277662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277662 eq873663
  have eq873852 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq873762
       have i₂ := eq277753 x
       grind)
    | exact superpose eq277753 eq873762
    | exact resolve eq873762 eq277753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873762
  have eq873920 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq279924 x X0
       have i₂ := eq873852
       grind)
    | exact superpose eq873852 eq279924
    | exact resolve eq279924 eq873852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279924
  have eq873932 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq279982 x X0
       have i₂ := eq873852
       grind)
    | exact superpose eq873852 eq279982
    | exact resolve eq279982 eq873852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279982
  have eq873985 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq873852
       grind)
    | exact superpose eq873852 eq10
    | exact resolve eq10 eq873852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874615 : x = (M.op x x) := by
    first
    | (have i₁ := eq873985
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq873985
    | exact resolve eq873985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873985
  have eq874652 : ∀ X0 : G, (M.op (τ (σ (M.op x x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq873932 X0
       have i₂ := eq277753 x
       grind)
    | exact superpose eq277753 eq873932
    | exact resolve eq873932 eq277753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873932
  have eq874664 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq873920 X0
       have i₂ := eq277753 x
       grind)
    | exact superpose eq277753 eq873920
    | exact resolve eq873920 eq277753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277753 eq873920
  have eq874752 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq874652 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq874652
    | exact resolve eq874652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874652
  have eq874764 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq874664 X0
       have i₂ := eq873852
       grind)
    | exact superpose eq873852 eq874664
    | exact resolve eq874664 eq873852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873852 eq874664
  have eq874826 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq874752 X0
       have i₂ := eq874615
       grind)
    | exact superpose eq874615 eq874752
    | exact resolve eq874752 eq874615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874615 eq874752
  have eq882391 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq874764 (σ y)
       grind)
    | exact superpose eq874764 eq16
    | exact resolve eq16 eq874764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874764
  have eq883218 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq882391
       have i₂ := eq874826 y
       grind)
    | exact superpose eq874826 eq882391
    | exact resolve eq882391 eq874826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874826 eq882391
  have eq883219 : False := by grind
  exact eq883219

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_y_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
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
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq80 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq43
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq43 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op (M.op (σ (k X0 X0)) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X1
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq258 : ∀ X0 X1 : G, (M.op (M.op (σ (k X0 X0)) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq254 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq259 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq262 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq259 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq259 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq294 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq262 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq33 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq33 eq262
    | (have j0 := eq262 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq262 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq303 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | (have i₁ := eq294 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq304 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op X0 X0) X0))) = (M.op X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq303 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq476 : ∀ X0 X1 : G, (M.op (M.op (σ (k (τ X0) (τ X0))) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq258 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq258
    | exact resolve eq258 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq499 : ∀ X0 X1 : G, (M.op (M.op (k (σ (τ X0)) X0) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq476
    | (have j0 := eq476 X0 X1
       grind)
    | exact resolve eq476 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq476
  have eq503 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq499 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq499
    | (have j0 := eq499 X0 X1
       grind)
    | exact resolve eq499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq512 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq503 (τ X0) X1
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq503
    | (have j0 := eq503 (τ X0) X1
       grind)
    | exact resolve eq503 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq563 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X1 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq603 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq563
    | (have j0 := eq563 X0 X1
       grind)
    | exact resolve eq563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq651 : ∀ X0 X1 : G, (k (τ X0) (M.op (M.op X1 X1) X1)) = (τ (M.op X0 (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq304 X1 X0
       grind)
    | exact superpose eq304 eq30
    | exact resolve eq30 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq692 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (M.op X1 X1) X1)) = (τ (M.op X0 (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X1
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq651
    | exact resolve eq651 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq651
  have eq1144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq247
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq247
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq247 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq1145 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1144
  have eq4135 : ∀ X0 X1 : G, (τ (σ (M.op (M.op X0 X0) X0))) = (M.op (τ (M.op (M.op X1 X1) X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 (M.op (M.op X1 X1) X1) X0
       have i₂ := eq19 X1 (σ (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq19 eq692
    | exact resolve eq692 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq4200 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (τ (M.op (M.op X1 X1) X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4135 X0 X1
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq4135
    | exact resolve eq4135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq4665 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op (M.op X0 X0) X0)) (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0)))
       have i₂ := eq4200 (τ (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq4200 eq9
    | exact resolve eq9 eq4200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4200
  have eq4706 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4665 X0 X1
       have i₂ := eq19 (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))
       grind)
    | (have i₁ := eq4665 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op (τ (M.op (M.op X0 X0) X0)) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0))) (τ (M.op (M.op X0 X0) X0)))
       grind)
    | exact superpose eq19 eq4665
    | exact resolve eq4665 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4665
  have eq16102 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq512 X0 X2
       grind)
    | exact superpose eq512 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq512 X0 X2
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq512 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op (τ (k X0 X0)) (τ X0))
       have r₂ := eq512 X0 (M.op (τ (k X0 X0)) (τ X0))
       grind)
    | exact resolve eq12 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq16162 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq16102 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16102
  have eq34694 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op (M.op (τ (k X1 X1)) (τ X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X1 X0
       have i₂ := eq16162 X1 (τ X0) X2
       grind)
    | exact superpose eq16162 eq43
    | (have j1 := eq16162 X1 X1 X2
       grind)
    | exact resolve eq43 eq16162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq16162
  have eq37156 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1145
       grind)
    | exact superpose eq1145 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1145
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1145
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1145
       grind)
    | exact resolve eq13 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq37184 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq37156
  have eq37185 : x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq37184
  have eq66952 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k X0 X0)) (τ X0)) X1) = X1 ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (τ X0) X1
       have i₂ := eq34694 X0 X0 X2
       grind)
    | exact superpose eq34694 eq19
    | (have j1 := eq34694 X0 X0 X1
       grind)
    | exact resolve eq19 eq34694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq34694
  have eq152311 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op (M.op (τ (k X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66952 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66952
  have eq152312 : ∀ X0 X1 : G, (M.op (M.op (τ (k X0 X0)) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq152311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152311
  have eq152490 : ∀ X0 X1 : G, (M.op (M.op (k X0 (τ (σ X0))) (τ (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152312 (σ X0) X1
       have i₂ := eq40 X0 (σ X0)
       grind)
    | exact superpose eq40 eq152312
    | exact resolve eq152312 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq152312
  have eq152954 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152490 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq152490
    | exact resolve eq152490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152490
  have eq153381 : ∀ X0 X1 : G, (M.op (M.op (σ (k X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152954 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq152954
    | exact resolve eq152954 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153487 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (k X0 X0) X0) (M.op (k X0 X0) X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4706 (M.op (k X0 X0) X0) X1
       have i₂ := eq152954 X0 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq152954 eq4706
    | exact resolve eq4706 eq152954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706
  have eq153774 : ∀ X0 X1 : G, (M.op (τ (M.op (k X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq153487 X0 X1
       have i₂ := eq152954 X0 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq152954 eq153487
    | exact resolve eq153487 eq152954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152954 eq153487
  have eq153878 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (k X0 X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq153774 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq153774
    | exact resolve eq153774 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153774
  have eq659015 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq80 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq659017 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq659015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659015
  have eq659068 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq659017 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq659017
    | exact resolve eq659017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659017
  have eq659371 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq659068 X0
       have i₂ := eq30 (σ X0) X0
       grind)
    | exact superpose eq30 eq659068
    | (have j0 := eq659068 X0
       grind)
    | exact resolve eq659068 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq659068
  have eq659391 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq659371 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq659371
    | (have j0 := eq659371 X0
       grind)
    | exact resolve eq659371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659371
  have eq659407 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq659391 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq659391 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq659391 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659391
  have eq659563 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq153381 X0 X1
       have i₂ := eq659407 X0
       grind)
    | exact superpose eq659407 eq153381
    | exact resolve eq153381 eq659407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153381
  have eq659632 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq153878 X0 X1
       have i₂ := eq659407 X0
       grind)
    | exact superpose eq659407 eq153878
    | exact resolve eq153878 eq659407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153878
  have eq659735 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq255 X0 X0
       have i₂ := eq659407 X0
       grind)
    | exact superpose eq659407 eq255
    | (have j0 := eq255 X0 X0
       grind)
    | exact resolve eq255 eq659407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659850 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq659407 (σ X0)
       grind)
    | exact superpose eq659407 eq15
    | exact resolve eq15 eq659407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659979 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq659735 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659735
  have eq660079 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq659850 X0
       have i₂ := eq659407 X0
       grind)
    | exact superpose eq659407 eq659850
    | exact resolve eq659850 eq659407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659407 eq659850
  have eq679966 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq255 x y
       have i₂ := eq37185
       grind)
    | exact superpose eq37185 eq255
    | (have j0 := eq255 x y
       grind)
    | exact resolve eq255 eq37185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq37185
  have eq680004 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq679966
  have eq680005 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq680004
  have eq680015 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq680005
       have i₂ := eq660079 x
       grind)
    | exact superpose eq660079 eq680005
    | exact resolve eq680005 eq660079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680005
  have eq1421874 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq680015
       grind)
    | exact superpose eq680015 eq16
    | exact resolve eq16 eq680015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421879 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq680015
       grind)
    | exact superpose eq680015 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq680015
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq680015
       grind)
    | exact resolve eq13 eq680015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680015
  have eq1421956 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1421879
  have eq1421958 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq659979 x
       grind)
    | (have r₁ := eq1421956
       have r₂ := eq659979 x
       grind)
    | exact resolve eq1421956 eq659979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421956
  have eq1421959 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1421958
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1421958
    | exact resolve eq1421958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421958
  have eq1421960 : x = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1421959
       have i₂ := eq660079 x
       grind)
    | exact superpose eq660079 eq1421959
    | exact resolve eq1421959 eq660079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421959
  have eq1424274 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq659979 x
       have i₂ := eq1421960
       grind)
    | exact superpose eq1421960 eq659979
    | (have j0 := eq659979 x
       grind)
    | (have r₁ := eq659979 x
       have r₂ := eq1421960
       grind)
    | exact resolve eq659979 eq1421960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421960
  have eq1424384 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq1424274
  have eq1424390 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have j1 := eq659979 x
       grind)
    | (have r₁ := eq1424384
       have r₂ := eq659979 x
       grind)
    | exact resolve eq1424384 eq659979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424384
  have eq1424489 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1424390
       have i₂ := eq660079 x
       grind)
    | exact superpose eq660079 eq1424390
    | exact resolve eq1424390 eq660079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424390
  have eq1426740 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq603 y x
       have i₂ := eq1424489
       grind)
    | exact superpose eq1424489 eq603
    | (have j0 := eq603 y x
       grind)
    | exact resolve eq603 eq1424489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq1424489
  have eq1427489 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1426740
       have r₂ := eq1421874
       grind)
    | exact resolve eq1426740 eq1421874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426740
  have eq1435110 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1421874
       have i₂ := eq1427489
       grind)
    | exact superpose eq1427489 eq1421874
    | exact resolve eq1421874 eq1427489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421874 eq1427489
  have eq1435191 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq1435110
  have eq1435192 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq1435191
  have eq1435440 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq659979 x
       have i₂ := eq1435192
       grind)
    | exact superpose eq1435192 eq659979
    | (have j0 := eq659979 x
       grind)
    | (have r₁ := eq659979 x
       have r₂ := eq1435192
       grind)
    | exact resolve eq659979 eq1435192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435192
  have eq1435550 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq1435440
  have eq1435556 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq659979 x
       grind)
    | (have r₁ := eq1435550
       have r₂ := eq659979 x
       grind)
    | exact resolve eq1435550 eq659979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659979 eq1435550
  have eq1435655 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1435556
       have i₂ := eq660079 x
       grind)
    | exact superpose eq660079 eq1435556
    | exact resolve eq1435556 eq660079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435556
  have eq1438181 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq659563 x X0
       have i₂ := eq1435655
       grind)
    | exact superpose eq1435655 eq659563
    | exact resolve eq659563 eq1435655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659563
  have eq1438182 : ∀ X0 : G, (M.op (τ (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq659632 x X0
       have i₂ := eq1435655
       grind)
    | exact superpose eq1435655 eq659632
    | exact resolve eq659632 eq1435655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659632
  have eq1438245 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1435655
       grind)
    | exact superpose eq1435655 eq10
    | exact resolve eq10 eq1435655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438986 : x = (M.op x x) := by
    first
    | (have i₁ := eq1438245
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1438245
    | exact resolve eq1438245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438245
  have eq1439033 : ∀ X0 : G, (M.op (τ (σ (M.op x x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1438182 X0
       have i₂ := eq660079 x
       grind)
    | exact superpose eq660079 eq1438182
    | exact resolve eq1438182 eq660079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438182
  have eq1439034 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1438181 X0
       have i₂ := eq660079 x
       grind)
    | exact superpose eq660079 eq1438181
    | exact resolve eq1438181 eq660079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660079 eq1438181
  have eq1439170 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1439033 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1439033
    | exact resolve eq1439033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439033
  have eq1439171 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1439034 X0
       have i₂ := eq1435655
       grind)
    | exact superpose eq1435655 eq1439034
    | exact resolve eq1439034 eq1435655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435655 eq1439034
  have eq1439264 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1439170 X0
       have i₂ := eq1438986
       grind)
    | exact superpose eq1438986 eq1439170
    | exact resolve eq1439170 eq1438986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438986 eq1439170
  have eq1443657 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1439171 (σ y)
       grind)
    | exact superpose eq1439171 eq16
    | exact resolve eq16 eq1439171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439171
  have eq1444751 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1443657
       have i₂ := eq1439264 y
       grind)
    | exact superpose eq1439264 eq1443657
    | exact resolve eq1443657 eq1439264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439264 eq1443657
  have eq1444752 : False := by grind
  exact eq1444752

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_pyx_pyx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq60
  have eq83 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq138 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq19 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq171 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x (M.op X0 X0)
       have i₂ := eq138 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq138 eq9
    | exact resolve eq9 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq236 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq171 (σ X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq171
    | exact resolve eq171 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq171
  have eq268 : ∀ X0 X1 : G, (M.op (σ (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq236 (σ (M.op X0 X0)) X1
       have i₂ := eq236 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq236 eq236
    | exact resolve eq236 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (σ X1) X1
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq448 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq455 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq448 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq448 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq470 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq455 X0 X1
       have j1 := eq83 X1 (σ X0)
       grind)
    | (have r₁ := eq455 X0 X0
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq455 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq455
  have eq479 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq470
    | (have j0 := eq470 X0 X1
       grind)
    | exact resolve eq470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq480 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq542 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq480 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq480
    | exact resolve eq480 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq554 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq480 x y
       grind)
    | exact superpose eq480 eq16
    | exact resolve eq16 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq236 X1 (σ X0)
       have i₂ := eq480 (M.op X1 X1) X0
       grind)
    | exact superpose eq480 eq236
    | exact resolve eq236 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq480
  have eq681 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (M.op X1 X1))
       have i₂ := eq557 X0 X1
       grind)
    | exact superpose eq557 eq10
    | exact resolve eq10 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq700 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq681
    | exact resolve eq681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq770 : ∀ X0 X1 : G, (k X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq700 X1 (σ (σ (M.op X0 X0)))
       have i₂ := eq268 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq268 eq700
    | exact resolve eq700 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq700
  have eq941 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (k X1 (k (τ X0) (σ (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 (σ (M.op X2 X2)) X1
       have i₂ := eq770 X2 X0
       grind)
    | exact superpose eq770 eq22
    | exact resolve eq22 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq953 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (M.op (k X0 (σ (σ (M.op X2 X2)))) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq941 X0 X1 X2
       have i₂ := eq542 X0 (σ (M.op X2 X2)) X1
       grind)
    | exact superpose eq542 eq941
    | exact resolve eq941 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq941
  have eq963 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1 x
       have i₂ := eq770 x X0
       grind)
    | exact superpose eq770 eq953
    | exact resolve eq953 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq953
  have eq1107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq963 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq963
    | exact resolve eq963 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1343 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq554
       have i₂ := eq1107 y x
       grind)
    | exact superpose eq1107 eq554
    | exact resolve eq554 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq1107
  have eq1344 : False := by grind
  exact eq1344
