import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,X) = Y then Y else if X = Y then m(Y,X) else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_x_y_pyx_x_y_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq51 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq59 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq44
  have eq67 : y ≠ (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq121 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq489 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq681 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq5873 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq682 x y
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq682
    | (have j0 := eq682 x y
       grind)
    | exact resolve eq682 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq5904 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5873
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5873
    | exact resolve eq5873 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873
  have eq5988 : (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5904
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5904
    | exact resolve eq5904 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5904
  have eq6072 : (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5988
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5988
    | exact resolve eq5988 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988
  have eq6156 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6072
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6072
    | exact resolve eq6072 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6072
  have eq6239 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6156
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6156
    | exact resolve eq6156 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156
  have eq6321 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq6239
    | exact resolve eq6239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239
  have eq6403 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6321
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6321
    | exact resolve eq6321 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6321
  have eq6470 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6403
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6403
    | exact resolve eq6403 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403
  have eq6478 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq6470
    | exact resolve eq6470 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6470
  have eq12461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12461
    | exact resolve eq12461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12461
  have eq12473 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq12462
       have r₂ := eq28
       grind)
    | exact resolve eq12462 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12462
  have eq12475 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12473
    | exact resolve eq12473 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12473
  have eq12477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12475
    | exact resolve eq12475 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12475
  have eq12479 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12477 eq68
    | (have r₁ := eq68
       have r₂ := eq12477
       grind)
    | exact resolve eq68 eq12477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq12481 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12477 eq28
    | exact resolve eq28 eq12477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12477
  have eq12483 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12479
  have eq12484 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12483
  have eq12490 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12484 eq81
    | exact resolve eq81 eq12484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12491 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12484 eq96
    | exact resolve eq96 eq12484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12484
  have eq12503 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12491
  have eq12513 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12503
       have r₂ := eq12481
       grind)
    | exact resolve eq12503 eq12481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12481 eq12503
  have eq12514 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq12490
    | exact resolve eq12490 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12490
  have eq12519 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq12514
       have r₂ := eq67
       grind)
    | exact resolve eq12514 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12514
  have eq12521 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12513 eq52
    | (have r₁ := eq52
       have r₂ := eq12513
       grind)
    | exact resolve eq52 eq12513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12522 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12513 eq28
    | exact resolve eq28 eq12513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12513
  have eq12523 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq12521
  have eq12537 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq681 x y
       have i₂ := eq12519
       grind)
    | exact superpose eq12519 eq681
    | (have j0 := eq681 x y
       grind)
    | exact resolve eq681 eq12519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq12519
  have eq12540 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12537
  have eq12543 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12540
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12540
    | exact resolve eq12540 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12540
  have eq12554 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12543
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12543
    | exact resolve eq12543 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12543
  have eq12555 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12554
  have eq12556 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12555
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12555
    | exact resolve eq12555 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12555
  have eq12557 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12556
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12556
    | exact resolve eq12556 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12556
  have eq12558 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12557
    | exact resolve eq12557 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12557
  have eq12559 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12558
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12558
    | exact resolve eq12558 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12558
  have eq12560 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12559
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12559
    | exact resolve eq12559 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12559
  have eq12561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12560
    | exact resolve eq12560 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12560
  have eq12562 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12561
  have eq12566 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12562 eq28
    | exact resolve eq28 eq12562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12562
  have eq12578 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12523 eq96
    | exact resolve eq96 eq12523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq12523
  have eq12592 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12578
  have eq12603 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12592
       have r₂ := eq12522
       grind)
    | exact resolve eq12592 eq12522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12522 eq12592
  have eq12611 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq12603 eq30
    | exact resolve eq30 eq12603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12603
  have eq12728 : x = y ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq12611
    | exact resolve eq12611 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12611
  have eq12729 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12728
  have eq12731 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12729 eq21
    | exact resolve eq21 eq12729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12735 : y ≠ y ∨ x = y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12729 eq67
    | (have r₁ := eq67
       have r₂ := eq12729
       grind)
    | exact resolve eq67 eq12729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq12729
  have eq12796 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq12735
  have eq12797 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq12796
  have eq12858 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12731
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12731
    | exact resolve eq12731 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12731
  have eq12869 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12858 eq81
    | exact resolve eq81 eq12858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq12925 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12858 eq12566
    | (have r₁ := eq12566
       have r₂ := eq12858
       grind)
    | exact resolve eq12566 eq12858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12566
  have eq12928 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12925
  have eq12929 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12928
  have eq12983 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq132 eq12869
    | exact resolve eq12869 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12869
  have eq12993 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq12797
       grind)
    | exact superpose eq12797 eq74
    | exact resolve eq74 eq12797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12797
  have eq13018 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12993
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12993
    | exact resolve eq12993 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12993
  have eq13030 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12858 eq13018
    | exact resolve eq13018 eq12858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12858 eq13018
  have eq13057 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq13030
  have eq13074 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq13057 eq132
    | exact resolve eq132 eq13057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq13057
  have eq13093 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq13074
    | exact resolve eq13074 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13074
  have eq13133 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12929 eq52
    | (have r₁ := eq52
       have r₂ := eq12929
       grind)
    | exact resolve eq52 eq12929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12929
  have eq13134 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13133
  have eq13616 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12983 eq13093
    | exact resolve eq13093 eq12983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12983 eq13093
  have eq13623 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq13616
  have eq13655 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq13623
       grind)
    | exact superpose eq13623 eq74
    | exact resolve eq74 eq13623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13623
  have eq13685 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq13655
    | exact resolve eq13655 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13655
  have eq15530 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13134 eq13685
    | exact resolve eq13685 eq13134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13134 eq13685
  have eq15538 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq15530
  have eq15565 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15538 eq29
    | exact resolve eq29 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15538
  have eq15709 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq15565
    | exact resolve eq15565 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15565
  have eq15710 : x = (M.op x y) ∨ x = y := by grind
  clear eq15709
  have eq15712 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq15710 eq21
    | exact resolve eq21 eq15710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15714 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq15710 eq51
    | (have r₁ := eq51
       have r₂ := eq15710
       grind)
    | exact resolve eq51 eq15710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq15775 : x = (k y x) ∨ x = y := by grind
  clear eq15714
  have eq15837 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq15712
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15712
    | exact resolve eq15712 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq16051 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq15837 eq27
    | exact resolve eq27 eq15837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16202 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq15775
       grind)
    | exact superpose eq15775 eq74
    | exact resolve eq74 eq15775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq15775
  have eq16236 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16202
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16202
    | exact resolve eq16202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16202
  have eq16247 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq16051 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq16051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16051
  have eq16251 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq16247
       have r₂ := eq28
       grind)
    | exact resolve eq16247 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16247
  have eq16469 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15837 eq16236
    | exact resolve eq16236 eq15837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16236
  have eq16512 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq16469
  have eq18451 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq15837 eq6478
    | exact resolve eq6478 eq15837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6478 eq15837
  have eq18477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq18451
       have r₂ := eq16512
       grind)
    | exact resolve eq18451 eq16512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18451
  have eq18478 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18477
       have r₂ := eq28
       grind)
    | exact resolve eq18477 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477
  have eq113292 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16251
       have r₂ := eq18478
       grind)
    | exact resolve eq16251 eq18478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16251 eq18478
  have eq113311 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq113292 eq16512
    | exact resolve eq16512 eq113292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16512 eq113292
  have eq113388 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq113311
  have eq113641 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq113388 eq30
    | exact resolve eq30 eq113388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq113388
  have eq114004 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq113641
    | exact resolve eq113641 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq113641
  have eq114143 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq114004 eq15710
    | exact resolve eq15710 eq114004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15710 eq114004
  have eq114434 : x = y := by grind
  clear eq114143
  have eq114811 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq114434
       grind)
    | exact superpose eq114434 eq19
    | exact resolve eq19 eq114434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq114812 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq114434
       grind)
    | exact superpose eq114434 eq25
    | exact resolve eq25 eq114434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq114434
  have eq115074 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq114812
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq114812
    | exact resolve eq114812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114812
  have eq115077 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq115074 eq27
    | exact resolve eq27 eq115074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq115338 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59
       have i₂ := eq114811
       grind)
    | exact superpose eq114811 eq59
    | exact resolve eq59 eq114811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq115339 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq114811
       grind)
    | exact superpose eq114811 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq114811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114811
  have eq115342 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq115338
    | exact resolve eq115338 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115338
  have eq115411 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq115414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115077 eq115411
    | exact resolve eq115411 eq115077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115411
  have eq115428 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq115414
       have r₂ := eq28
       grind)
    | exact resolve eq115414 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115414
  have eq115433 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115077 eq115428
    | exact resolve eq115428 eq115077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115428
  have eq115440 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115433 eq28
    | exact resolve eq28 eq115433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115441 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115433 eq52
    | (have r₁ := eq52
       have r₂ := eq115433
       grind)
    | exact resolve eq52 eq115433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq115433
  have eq115446 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq115441
  have eq115450 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115074 eq115446
    | exact resolve eq115446 eq115074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115074 eq115446
  have eq115522 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115450 eq50
    | exact resolve eq50 eq115450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq115553 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115450 eq115342
    | exact resolve eq115342 eq115450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115342 eq115450
  have eq115575 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq115553
  have eq115583 : x = (M.op x y) := by
    first
    | (have r₁ := eq115575
       have r₂ := eq115440
       grind)
    | exact resolve eq115575 eq115440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115440 eq115575
  have eq115591 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq115522
    | exact resolve eq115522 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq115522
  have eq115599 : x = (k x x) := by
    first
    | (have r₁ := eq115591
       have r₂ := eq115339
       grind)
    | exact resolve eq115591 eq115339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115339 eq115591
  have eq115603 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq115583 eq21
    | exact resolve eq21 eq115583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq115583
  have eq115928 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq115603
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq115603
    | exact resolve eq115603 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115603
  have eq116315 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq489 x
       have i₂ := eq115599
       grind)
    | exact superpose eq115599 eq489
    | (have j0 := eq489 x
       grind)
    | exact resolve eq489 eq115599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq115599
  have eq116318 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq116315
  have eq116325 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116318
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq116318
    | exact resolve eq116318 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq116318
  have eq116343 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115077 eq116325
    | exact resolve eq116325 eq115077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115077 eq116325
  have eq116359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115928 eq116343
    | exact resolve eq116343 eq115928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115928 eq116343
  have eq116373 : False := by grind
  exact eq116373

/-- `x □ y = if m(Y,X) = Y then Y else if X = Y then m(Y,Y) else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_x_y_pyx_x_y_pyy_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq51 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq59 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq44
  have eq67 : y ≠ (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq121 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq489 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq681 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq5873 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq682 x y
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq682
    | (have j0 := eq682 x y
       grind)
    | exact resolve eq682 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq5904 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5873
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5873
    | exact resolve eq5873 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873
  have eq5988 : (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5904
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5904
    | exact resolve eq5904 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5904
  have eq6072 : (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5988
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5988
    | exact resolve eq5988 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988
  have eq6156 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6072
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6072
    | exact resolve eq6072 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6072
  have eq6239 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6156
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6156
    | exact resolve eq6156 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156
  have eq6321 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq6239
    | exact resolve eq6239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239
  have eq6403 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6321
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6321
    | exact resolve eq6321 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6321
  have eq6470 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6403
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6403
    | exact resolve eq6403 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403
  have eq6478 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq6470
    | exact resolve eq6470 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6470
  have eq12461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12461
    | exact resolve eq12461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12461
  have eq12473 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq12462
       have r₂ := eq28
       grind)
    | exact resolve eq12462 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12462
  have eq12475 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12473
    | exact resolve eq12473 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12473
  have eq12477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12475
    | exact resolve eq12475 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12475
  have eq12479 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12477 eq68
    | (have r₁ := eq68
       have r₂ := eq12477
       grind)
    | exact resolve eq68 eq12477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq12481 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12477 eq28
    | exact resolve eq28 eq12477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12477
  have eq12483 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12479
  have eq12484 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12483
  have eq12490 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12484 eq81
    | exact resolve eq81 eq12484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12491 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12484 eq96
    | exact resolve eq96 eq12484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12484
  have eq12503 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12491
  have eq12513 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12503
       have r₂ := eq12481
       grind)
    | exact resolve eq12503 eq12481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12481 eq12503
  have eq12514 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq12490
    | exact resolve eq12490 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12490
  have eq12519 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq12514
       have r₂ := eq67
       grind)
    | exact resolve eq12514 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12514
  have eq12521 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12513 eq52
    | (have r₁ := eq52
       have r₂ := eq12513
       grind)
    | exact resolve eq52 eq12513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12522 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12513 eq28
    | exact resolve eq28 eq12513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12513
  have eq12523 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq12521
  have eq12537 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq681 x y
       have i₂ := eq12519
       grind)
    | exact superpose eq12519 eq681
    | (have j0 := eq681 x y
       grind)
    | exact resolve eq681 eq12519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq12519
  have eq12540 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12537
  have eq12543 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12540
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12540
    | exact resolve eq12540 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12540
  have eq12554 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12543
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12543
    | exact resolve eq12543 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12543
  have eq12555 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12554
  have eq12556 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12555
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12555
    | exact resolve eq12555 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12555
  have eq12557 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12556
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12556
    | exact resolve eq12556 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12556
  have eq12558 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12557
    | exact resolve eq12557 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12557
  have eq12559 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12558
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12558
    | exact resolve eq12558 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12558
  have eq12560 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12559
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12559
    | exact resolve eq12559 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12559
  have eq12561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12560
    | exact resolve eq12560 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12560
  have eq12562 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12561
  have eq12566 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12562 eq28
    | exact resolve eq28 eq12562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12562
  have eq12578 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12523 eq96
    | exact resolve eq96 eq12523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq12523
  have eq12592 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12578
  have eq12603 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12592
       have r₂ := eq12522
       grind)
    | exact resolve eq12592 eq12522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12522 eq12592
  have eq12611 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq12603 eq30
    | exact resolve eq30 eq12603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12603
  have eq12728 : x = y ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq12611
    | exact resolve eq12611 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12611
  have eq12729 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12728
  have eq12731 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12729 eq21
    | exact resolve eq21 eq12729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12735 : y ≠ y ∨ x = y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12729 eq67
    | (have r₁ := eq67
       have r₂ := eq12729
       grind)
    | exact resolve eq67 eq12729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq12729
  have eq12796 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq12735
  have eq12797 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq12796
  have eq12858 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12731
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12731
    | exact resolve eq12731 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12731
  have eq12869 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12858 eq81
    | exact resolve eq81 eq12858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq12925 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12858 eq12566
    | (have r₁ := eq12566
       have r₂ := eq12858
       grind)
    | exact resolve eq12566 eq12858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12566
  have eq12928 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12925
  have eq12929 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12928
  have eq12983 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq132 eq12869
    | exact resolve eq12869 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12869
  have eq12993 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq12797
       grind)
    | exact superpose eq12797 eq74
    | exact resolve eq74 eq12797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12797
  have eq13018 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12993
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12993
    | exact resolve eq12993 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12993
  have eq13030 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12858 eq13018
    | exact resolve eq13018 eq12858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12858 eq13018
  have eq13057 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq13030
  have eq13074 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq13057 eq132
    | exact resolve eq132 eq13057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq13057
  have eq13093 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq13074
    | exact resolve eq13074 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13074
  have eq13133 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12929 eq52
    | (have r₁ := eq52
       have r₂ := eq12929
       grind)
    | exact resolve eq52 eq12929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12929
  have eq13134 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13133
  have eq13616 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12983 eq13093
    | exact resolve eq13093 eq12983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12983 eq13093
  have eq13623 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq13616
  have eq13655 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq13623
       grind)
    | exact superpose eq13623 eq74
    | exact resolve eq74 eq13623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13623
  have eq13685 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq13655
    | exact resolve eq13655 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13655
  have eq15530 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13134 eq13685
    | exact resolve eq13685 eq13134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13134 eq13685
  have eq15538 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq15530
  have eq15565 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15538 eq29
    | exact resolve eq29 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15538
  have eq15709 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq15565
    | exact resolve eq15565 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15565
  have eq15710 : x = (M.op x y) ∨ x = y := by grind
  clear eq15709
  have eq15712 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq15710 eq21
    | exact resolve eq21 eq15710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15714 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq15710 eq51
    | (have r₁ := eq51
       have r₂ := eq15710
       grind)
    | exact resolve eq51 eq15710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq15775 : x = (k y x) ∨ x = y := by grind
  clear eq15714
  have eq15837 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq15712
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15712
    | exact resolve eq15712 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq16051 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq15837 eq27
    | exact resolve eq27 eq15837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16202 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq15775
       grind)
    | exact superpose eq15775 eq74
    | exact resolve eq74 eq15775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq15775
  have eq16236 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16202
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16202
    | exact resolve eq16202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16202
  have eq16247 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq16051 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq16051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16051
  have eq16251 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq16247
       have r₂ := eq28
       grind)
    | exact resolve eq16247 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16247
  have eq16469 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15837 eq16236
    | exact resolve eq16236 eq15837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16236
  have eq16512 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq16469
  have eq18451 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq15837 eq6478
    | exact resolve eq6478 eq15837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6478 eq15837
  have eq18477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq18451
       have r₂ := eq16512
       grind)
    | exact resolve eq18451 eq16512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18451
  have eq18478 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18477
       have r₂ := eq28
       grind)
    | exact resolve eq18477 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477
  have eq113292 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16251
       have r₂ := eq18478
       grind)
    | exact resolve eq16251 eq18478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16251 eq18478
  have eq113311 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq113292 eq16512
    | exact resolve eq16512 eq113292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16512 eq113292
  have eq113388 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq113311
  have eq113641 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq113388 eq30
    | exact resolve eq30 eq113388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq113388
  have eq114004 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq113641
    | exact resolve eq113641 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq113641
  have eq114143 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq114004 eq15710
    | exact resolve eq15710 eq114004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15710 eq114004
  have eq114434 : x = y := by grind
  clear eq114143
  have eq114811 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq114434
       grind)
    | exact superpose eq114434 eq19
    | exact resolve eq19 eq114434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq114812 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq114434
       grind)
    | exact superpose eq114434 eq25
    | exact resolve eq25 eq114434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq114434
  have eq115074 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq114812
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq114812
    | exact resolve eq114812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114812
  have eq115077 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq115074 eq27
    | exact resolve eq27 eq115074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq115338 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59
       have i₂ := eq114811
       grind)
    | exact superpose eq114811 eq59
    | exact resolve eq59 eq114811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq115339 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq114811
       grind)
    | exact superpose eq114811 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq114811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114811
  have eq115342 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq115338
    | exact resolve eq115338 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115338
  have eq115411 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq115414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115077 eq115411
    | exact resolve eq115411 eq115077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115411
  have eq115428 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq115414
       have r₂ := eq28
       grind)
    | exact resolve eq115414 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115414
  have eq115433 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115077 eq115428
    | exact resolve eq115428 eq115077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115428
  have eq115440 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115433 eq28
    | exact resolve eq28 eq115433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115441 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115433 eq52
    | (have r₁ := eq52
       have r₂ := eq115433
       grind)
    | exact resolve eq52 eq115433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq115433
  have eq115446 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq115441
  have eq115450 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115074 eq115446
    | exact resolve eq115446 eq115074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115074 eq115446
  have eq115522 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115450 eq50
    | exact resolve eq50 eq115450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq115553 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115450 eq115342
    | exact resolve eq115342 eq115450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115342 eq115450
  have eq115575 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq115553
  have eq115583 : x = (M.op x y) := by
    first
    | (have r₁ := eq115575
       have r₂ := eq115440
       grind)
    | exact resolve eq115575 eq115440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115440 eq115575
  have eq115591 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq115522
    | exact resolve eq115522 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq115522
  have eq115599 : x = (k x x) := by
    first
    | (have r₁ := eq115591
       have r₂ := eq115339
       grind)
    | exact resolve eq115591 eq115339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115339 eq115591
  have eq115603 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq115583 eq21
    | exact resolve eq21 eq115583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq115583
  have eq115928 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq115603
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq115603
    | exact resolve eq115603 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115603
  have eq116315 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq489 x
       have i₂ := eq115599
       grind)
    | exact superpose eq115599 eq489
    | (have j0 := eq489 x
       grind)
    | exact resolve eq489 eq115599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq115599
  have eq116318 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq116315
  have eq116325 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116318
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq116318
    | exact resolve eq116318 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq116318
  have eq116343 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115077 eq116325
    | exact resolve eq116325 eq115077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115077 eq116325
  have eq116359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115928 eq116343
    | exact resolve eq116343 eq115928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115928 eq116343
  have eq116373 : False := by grind
  exact eq116373

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = X then m(X,Y) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_x_pxx_y_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq16
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 (σ X0) (σ X1)
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq38 eq70
    | (have j0 := eq70 (σ y) (σ X0)
       grind)
    | exact resolve eq70 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq70 x x
       grind)
    | exact superpose eq70 eq45
    | (have j1 := eq70 x x
       grind)
    | exact resolve eq45 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq46
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq46 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq70 y y
       grind)
    | exact superpose eq70 eq68
    | (have j1 := eq70 y y
       grind)
    | exact resolve eq68 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq51
       have i₂ := eq70 sF2 sF2
       grind)
    | exact superpose eq70 eq51
    | (have j1 := eq70 (σ x) (σ x)
       grind)
    | exact resolve eq51 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq101 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq99
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq95
  have eq103 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq92
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq105
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq70 sF3 sF3
       grind)
    | exact superpose eq70 eq80
    | (have j1 := eq70 (σ y) (σ y)
       grind)
    | exact resolve eq80 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq111 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq109
  have eq237 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq386 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq86 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq86 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq86 X0 X0
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq389 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq392 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq393 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq395 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq392 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq392
    | (have j0 := eq392 X0
       grind)
    | exact resolve eq392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq396 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq393 X0 (σ X0)
       have r₂ := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq393 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq393 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq3116 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq88 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq88
    | (have j0 := eq88 y
       grind)
    | exact resolve eq88 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq3118 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3116
  have eq3120 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3118
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq3118
    | exact resolve eq3118 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq3118
  have eq4330 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq395 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq395
    | (have j0 := eq395 (τ X0)
       grind)
    | exact resolve eq395 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq4340 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4330 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4330
    | (have j0 := eq4330 X0
       grind)
    | exact resolve eq4330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330
  have eq4358 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4340 X0
       have i₂ := eq40 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq40 eq4340
    | (have j0 := eq4340 X0
       grind)
    | exact resolve eq4340 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4340
  have eq4371 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4358 X0
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq4358
    | (have j0 := eq4358 X0
       grind)
    | exact resolve eq4358 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358
  have eq4378 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4371 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4371
    | (have j0 := eq4371 X0
       grind)
    | exact resolve eq4371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4371
  have eq4385 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4378 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4378
    | (have j0 := eq4378 X0
       grind)
    | exact resolve eq4378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4378
  have eq4490 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op X1 X1) ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq396 (τ X0) X1
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq396
    | (have j0 := eq396 (τ X0) X1
       grind)
    | exact resolve eq396 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq396
  have eq4498 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op X1 X1) ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4490 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4490
    | (have j0 := eq4490 X0 X1
       grind)
    | exact resolve eq4490 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4490
  have eq4504 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X0) ≠ X0 ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4498 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4498
    | (have j0 := eq4498 X0 X1
       grind)
    | exact resolve eq4498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4498
  have eq4510 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4504 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4504
    | (have j0 := eq4504 X0 X1
       grind)
    | exact resolve eq4504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4504
  have eq6233 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq237 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq237
    | exact resolve eq237 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq6338 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6233 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6233
    | (have j0 := eq6233 X0
       grind)
    | exact resolve eq6233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6233
  have eq13315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq106 eq70
    | (have j0 := eq70 (σ x) (σ y)
       grind)
    | exact resolve eq70 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq13316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq13315
    | exact resolve eq13315 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13315
  have eq13327 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq13316
       have r₂ := eq29
       grind)
    | exact resolve eq13316 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13316
  have eq13329 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq13327 eq101
    | exact resolve eq101 eq13327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq13335 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq13329
    | exact resolve eq13329 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13329
  have eq13844 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq13335 eq111
    | exact resolve eq111 eq13335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13335
  have eq13849 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq13844
  have eq13851 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq13849
    | exact resolve eq13849 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13849
  have eq13869 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq13851
       grind)
    | exact superpose eq13851 eq70
    | (have j0 := eq70 x y
       grind)
    | exact resolve eq70 eq13851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13851
  have eq13870 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq13869
  have eq13898 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq13870
       grind)
    | exact superpose eq13870 eq103
    | exact resolve eq103 eq13870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13901 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  have eq13902 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq13870
  have eq13904 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13901
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq13901
    | exact resolve eq13901 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13901
  have eq13906 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13898
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq13898
    | exact resolve eq13898 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13898
  have eq13939 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq13904
       grind)
    | exact superpose eq13904 eq67
    | exact resolve eq67 eq13904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13904
  have eq13962 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq13939
    | exact resolve eq13939 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13939
  have eq18151 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq13906
       have r₂ := eq13902
       grind)
    | exact resolve eq13906 eq13902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13902 eq13906
  have eq18419 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18151 eq4385
    | (have j0 := eq4385 (σ x)
       grind)
    | exact resolve eq4385 eq18151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4385
  have eq18425 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq18419
    | exact resolve eq18419 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18419
  have eq119074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18425 eq13962
    | exact resolve eq13962 eq18425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13962 eq18425
  have eq119092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq119074
  have eq119100 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq119092
       have r₂ := eq29
       grind)
    | exact resolve eq119092 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119092
  have eq119107 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq119917 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq119107 eq18151
    | exact resolve eq18151 eq119107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18151 eq119107
  have eq119937 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq119917
  have eq119953 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq119937 eq119100
    | exact resolve eq119100 eq119937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119100 eq119937
  have eq119960 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq119953
  have eq119987 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq119960
       grind)
    | exact superpose eq119960 eq70
    | (have j0 := eq70 y y
       grind)
    | exact resolve eq70 eq119960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119988 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq119987
  have eq120798 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq119988
  have eq120851 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq119960
       have i₂ := eq120798
       grind)
    | exact superpose eq120798 eq119960
    | exact resolve eq119960 eq120798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119960 eq120798
  have eq120859 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq120851
  have eq120875 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq120859
       grind)
    | exact superpose eq120859 eq102
    | exact resolve eq102 eq120859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120876 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq120859
  have eq120880 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120876
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq120876
    | exact resolve eq120876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120876
  have eq120881 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120875
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120875
    | exact resolve eq120875 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120875
  have eq121995 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3120 eq120881
    | exact resolve eq120881 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67
       have i₂ := eq120880
       grind)
    | exact superpose eq120880 eq67
    | exact resolve eq67 eq120880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120880
  have eq130189 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22 eq130114
    | exact resolve eq130114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130114
  have eq133930 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq121995
  have eq172521 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq133930 eq120881
    | exact resolve eq120881 eq133930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120881 eq133930
  have eq172574 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq172521
  have eq172586 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq172574
  have eq172589 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq172586
  have eq172593 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq172589
    | exact resolve eq172589 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172589
  have eq174987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq172593 eq130189
    | exact resolve eq130189 eq172593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq174987
  have eq175003 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq174992
       have r₂ := eq29
       grind)
    | exact resolve eq174992 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174992
  have eq175011 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq175003
  have eq175017 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq175011
    | exact resolve eq175011 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175011
  have eq176017 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq175017 eq130189
    | exact resolve eq130189 eq175017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130189 eq175017
  have eq176020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq176017
  have eq176038 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq176020
       have r₂ := eq29
       grind)
    | exact resolve eq176020 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176020
  have eq176045 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq176038
  have eq176051 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq176045
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq176045
    | exact resolve eq176045 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176045
  have eq177028 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67
       have i₂ := eq176051
       grind)
    | exact superpose eq176051 eq67
    | exact resolve eq67 eq176051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176051
  have eq177077 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22 eq177028
    | exact resolve eq177028 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177028
  have eq177183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq177077 eq172593
    | exact resolve eq172593 eq177077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172593
  have eq177188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq177183
  have eq177197 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq177188
       have r₂ := eq29
       grind)
    | exact resolve eq177188 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177188
  have eq178253 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq177197
  have eq178259 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq178253
    | exact resolve eq178253 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178253
  have eq179261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq178259 eq177077
    | exact resolve eq177077 eq178259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177077 eq178259
  have eq179264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq179261
  have eq179276 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq179264
       have r₂ := eq29
       grind)
    | exact resolve eq179264 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179264
  have eq179280 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq179276
       grind)
    | exact superpose eq179276 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq179276
       grind)
    | exact resolve eq13 eq179276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179281 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq179282 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq179280 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179280
  have eq180225 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq179281
       grind)
    | exact superpose eq179281 eq45
    | exact resolve eq45 eq179281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq179281
  have eq180296 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq180225
       have i₂ := eq179276
       grind)
    | exact superpose eq179276 eq180225
    | exact resolve eq180225 eq179276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180225
  have eq180424 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq180296
  have eq180430 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq180424
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180424
    | exact resolve eq180424 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180424
  have eq180472 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq180430 eq4510
    | (have j0 := eq4510 (σ x) X0
       grind)
    | (have r₁ := eq4510 (σ x) x
       have r₂ := eq180430
       grind)
    | exact resolve eq4510 eq180430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4510
  have eq180475 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq180430 eq70
    | (have j0 := eq70 (σ x) (σ x)
       grind)
    | exact resolve eq70 eq180430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180430
  have eq180476 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq180475
  have eq180479 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq180472 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180472
  have eq272250 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq179282 y
       grind)
    | exact superpose eq179282 eq46
    | (have j1 := eq179282 y
       grind)
    | exact resolve eq46 eq179282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq179282
  have eq272669 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq272250
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq272250
    | exact resolve eq272250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272250
  have eq272834 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22 eq272669
    | exact resolve eq272669 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272669
  have eq284688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq180479 eq272834
    | (have j1 := eq180479 (σ y)
       grind)
    | exact resolve eq272834 eq180479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180479 eq272834
  have eq284689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq284688
  have eq284977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq284689
    | exact resolve eq284689 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284689
  have eq285103 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq284977
       have r₂ := eq29
       grind)
    | exact resolve eq284977 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284977
  have eq286012 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq285103 eq111
    | exact resolve eq111 eq285103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq285103
  have eq286025 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq286012
  have eq286029 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq286025
    | exact resolve eq286025 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286025
  have eq286062 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq286029
       grind)
    | exact superpose eq286029 eq70
    | (have j0 := eq70 y y
       grind)
    | exact resolve eq70 eq286029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq286063 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq286062
  have eq287015 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq286063
  have eq319788 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq286029
       have i₂ := eq287015
       grind)
    | exact superpose eq287015 eq286029
    | exact resolve eq286029 eq287015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286029 eq287015
  have eq319800 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq319788
  have eq319849 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq319800
       grind)
    | exact superpose eq319800 eq102
    | exact resolve eq102 eq319800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq319858 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6338 y
       have i₂ := eq319800
       grind)
    | exact superpose eq319800 eq6338
    | exact resolve eq6338 eq319800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6338 eq319800
  have eq319859 : (σ (M.op x y)) = (σ (k y x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq319858
  have eq319866 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq319849
  have eq319869 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq319859
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq319859
    | exact resolve eq319859 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq319859
  have eq319875 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq319866
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq319866
    | exact resolve eq319866 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319866
  have eq319876 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq319869
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq319869
    | exact resolve eq319869 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319869
  have eq319881 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq319876
    | exact resolve eq319876 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319876
  have eq320731 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3120 eq319875
    | exact resolve eq319875 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq328695 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq320731
  have eq374802 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq328695 eq319875
    | exact resolve eq319875 eq328695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319875 eq328695
  have eq374883 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq374802
  have eq374926 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq374883
  have eq374938 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq374926
  have eq374943 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq28 eq374938
    | exact resolve eq374938 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374938
  have eq375581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq374943 eq319881
    | exact resolve eq319881 eq374943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319881 eq374943
  have eq375586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq375581
  have eq375601 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq375586
       have r₂ := eq29
       grind)
    | exact resolve eq375586 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375586
  have eq375607 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq375601 eq180476
    | exact resolve eq180476 eq375601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180476 eq375601
  have eq375780 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq375607
  have eq375848 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq179276
       have i₂ := eq375780
       grind)
    | exact superpose eq375780 eq179276
    | exact resolve eq179276 eq375780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179276 eq375780
  have eq376017 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq375848
  have eq376099 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq376017 eq31
    | exact resolve eq31 eq376017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq376017
  have eq376303 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq376099
    | exact resolve eq376099 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq376099
  have eq376304 : x = y := by grind
  clear eq376303
  have eq376305 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq376304
       grind)
    | exact superpose eq376304 eq20
    | exact resolve eq20 eq376304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq376306 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq376304
       grind)
    | exact superpose eq376304 eq26
    | exact resolve eq26 eq376304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq377054 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq376306
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq376306
    | exact resolve eq376306 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376306
  have eq377059 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq377054 eq28
    | exact resolve eq28 eq377054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq377437 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq376305
       grind)
    | exact superpose eq376305 eq103
    | exact resolve eq103 eq376305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq377528 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  have eq377540 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq377437
    | exact resolve eq377437 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377437
  have eq377563 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq377059 eq13327
    | exact resolve eq13327 eq377059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13327
  have eq377653 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq377659 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq377054 eq377563
    | exact resolve eq377563 eq377054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377563
  have eq377661 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq377054 eq377659
    | exact resolve eq377659 eq377054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377054 eq377659
  have eq377663 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq377059 eq377661
    | exact resolve eq377661 eq377059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377661
  have eq377664 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq377663
  have eq377667 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq377664
       have i₂ := eq376305
       grind)
    | exact superpose eq376305 eq377664
    | exact resolve eq377664 eq376305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377664
  have eq377669 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq377667
       have i₂ := eq376304
       grind)
    | exact superpose eq376304 eq377667
    | exact resolve eq377667 eq376304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377667
  have eq377671 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq377669
       have i₂ := eq376304
       grind)
    | exact superpose eq376304 eq377669
    | exact resolve eq377669 eq376304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376304 eq377669
  have eq377673 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq377671
       have i₂ := eq376305
       grind)
    | exact superpose eq376305 eq377671
    | exact resolve eq377671 eq376305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377671
  have eq377674 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq377673
  have eq377852 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq377674 eq377653
    | exact resolve eq377653 eq377674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377653 eq377674
  have eq377856 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq377059 eq377852
    | exact resolve eq377852 eq377059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377852
  have eq378540 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq377856 eq377540
    | exact resolve eq377540 eq377856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377540 eq377856
  have eq378558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq378540
  have eq378567 : x = (M.op x y) := by
    first
    | (have r₁ := eq378558
       have r₂ := eq29
       grind)
    | exact resolve eq378558 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378558
  have eq378580 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq378567 eq22
    | exact resolve eq22 eq378567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq378832 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq378567 eq377528
    | exact resolve eq377528 eq378567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377528
  have eq378837 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq378832
       have i₂ := eq376305
       grind)
    | exact superpose eq376305 eq378832
    | exact resolve eq378832 eq376305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376305 eq378832
  have eq379004 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq378580
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq378580
    | exact resolve eq378580 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378580
  have eq379006 : x = (k x x) := by
    first
    | exact superpose eq378567 eq378837
    | exact resolve eq378837 eq378567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378567 eq378837
  have eq380685 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq390 x
       have i₂ := eq379006
       grind)
    | exact superpose eq379006 eq390
    | (have j0 := eq390 x
       grind)
    | exact resolve eq390 eq379006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq379006
  have eq380707 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq380685
  have eq380727 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq380707
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq380707
    | exact resolve eq380707 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq380707
  have eq380753 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq377059 eq380727
    | exact resolve eq380727 eq377059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377059 eq380727
  have eq380775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq379004 eq380753
    | exact resolve eq380753 eq379004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379004 eq380753
  have eq380795 : False := by grind
  exact eq380795

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X) else if m(X,Y) = X then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_pxy_x_pyx_pyx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq32 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq40 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq43 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq45 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq50 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq54 : (M.op (σ x) (σ y)) = (σ (k x (τ (σ y)))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq40
       have i₂ := eq20 (σ y) x
       grind)
    | exact superpose eq20 eq40
    | exact resolve eq40 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq55 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq47 (τ X0)
       grind)
    | exact superpose eq47 eq23
    | (have j1 := eq47 (τ X0)
       grind)
    | exact resolve eq23 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq60 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | (have j0 := eq59 X0
       grind)
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (σ X0) = (σ (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X1) X0
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq51
    | (have j0 := eq51 (σ X0) X1
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (τ X0) X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 (τ X0) X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq55
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq55
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq95
  have eq108 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | (have j0 := eq64 X1 (σ X0)
       grind)
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq163 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq60
  have eq164 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq163 X0
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq163
    | (have j0 := eq163 X0
       grind)
    | exact resolve eq163 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq167 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq164 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq164
    | (have j0 := eq164 X0
       grind)
    | exact resolve eq164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq168 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq194 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (τ (σ (k X0 (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq168 (σ X0)
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq168
    | exact resolve eq168 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq211 : ∀ X0 : G, (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq194 X0
       have i₂ := eq9 (k X0 (τ (σ X0)))
       grind)
    | exact superpose eq9 eq194
    | exact resolve eq194 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq218 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq211 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq211
    | exact resolve eq211 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq258 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq218 (σ X0)
       grind)
    | exact superpose eq218 eq20
    | exact resolve eq20 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq218 (τ X0)
       grind)
    | exact superpose eq218 eq23
    | exact resolve eq23 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq260 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq259 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq259
    | exact resolve eq259 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq261 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq258 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq258
    | exact resolve eq258 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq265 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq260 X0
       have i₂ := eq218 X0
       grind)
    | exact superpose eq218 eq260
    | exact resolve eq260 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq266 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq261 X0
       have i₂ := eq218 X0
       grind)
    | exact superpose eq218 eq261
    | exact resolve eq261 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq261
  have eq269 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq282 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq266 X1
       grind)
    | exact superpose eq266 eq108
    | (have j0 := eq108 X0 X1
       grind)
    | exact resolve eq108 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq297 : (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq266 x
       grind)
    | exact superpose eq266 eq96
    | exact resolve eq96 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq298 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq266 x
       grind)
    | exact superpose eq266 eq55
    | exact resolve eq55 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq305 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq298
       have i₂ := eq266 y
       grind)
    | exact superpose eq266 eq298
    | exact resolve eq298 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq306 : (M.op x y) = (k x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq297
       have i₂ := eq266 y
       grind)
    | exact superpose eq266 eq297
    | exact resolve eq297 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq311 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq282
    | (have j0 := eq282 X0 X1
       grind)
    | exact resolve eq282 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq395 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 (σ X0)
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq35
    | exact resolve eq35 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq403 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq396 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq396
    | exact resolve eq396 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq404 : ∀ X0 : G, (σ (k X0 (τ (σ (M.op X0 X0))))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq395 X0
       have i₂ := eq20 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq20 eq395
    | exact resolve eq395 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq407 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq403 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq403
    | exact resolve eq403 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq408 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq404 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq404
    | exact resolve eq404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq409 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq407
  have eq410 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq408 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq408
    | exact resolve eq408 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq408
  have eq467 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (σ X1))
       have i₂ := eq269 X0 X1
       grind)
    | exact superpose eq269 eq10
    | (have j1 := eq269 X0 X1
       grind)
    | exact resolve eq10 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq579 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq311 X1 X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq311
    | (have j0 := eq311 X1 X0
       have j1 := eq51 X0 X1
       grind)
    | exact resolve eq311 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq311 y x
       have i₂ := eq306
       grind)
    | exact superpose eq306 eq311
    | (have j0 := eq311 y x
       grind)
    | exact resolve eq311 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq311 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq583
  have eq598 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq594
       have r₂ := eq16
       grind)
    | exact resolve eq594 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq602 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq598
       have r₂ := eq305
       grind)
    | exact resolve eq598 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq598
  have eq1503 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq467
    | (have j0 := eq467 X1 (τ X0)
       grind)
    | exact resolve eq467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq1538 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1503 X0 X1
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq1503
    | (have j0 := eq1503 X0 X1
       grind)
    | exact resolve eq1503 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq1503
  have eq1990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq409 x
       have i₂ := eq602
       grind)
    | exact superpose eq602 eq409
    | exact resolve eq409 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq2009 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1990
       have r₂ := eq16
       grind)
    | exact resolve eq1990 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq3584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq2009
       grind)
    | exact superpose eq2009 eq410
    | exact resolve eq410 eq2009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq3606 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq3584
       have r₂ := eq16
       grind)
    | exact resolve eq3584 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584
  have eq3621 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq306
       have i₂ := eq579 x y
       grind)
    | exact superpose eq579 eq306
    | (have j1 := eq579 x y
       grind)
    | exact resolve eq306 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq579
  have eq3622 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq3621
  have eq3630 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3622
       have r₂ := eq16
       grind)
    | exact resolve eq3622 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq3673 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq3606
       grind)
    | exact superpose eq3606 eq9
    | exact resolve eq9 eq3606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3606
  have eq14298 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq1538 X1 X0
       grind)
    | exact superpose eq1538 eq10
    | (have j1 := eq1538 X1 X0
       grind)
    | exact resolve eq10 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq14354 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14298 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14298
    | (have j0 := eq14298 X0 X1
       grind)
    | exact resolve eq14298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14298
  have eq14482 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X1))) ≠ X0 ∨ (k X0 X1) = X0 ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14354
  have eq14754 : ∀ X0 X1 : G, (σ (M.op (τ X1) X0)) ≠ X1 ∨ (k X1 (σ X0)) = X1 ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14482 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14482
    | (have j0 := eq14482 X1 (σ X0)
       grind)
    | exact resolve eq14482 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14482
  have eq14792 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (σ (M.op (τ X1) X0)) ≠ X1 ∨ (k X1 (σ X0)) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14754 X0 X1
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq14754
    | (have j0 := eq14754 X0 X1
       grind)
    | exact resolve eq14754 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14754
  have eq14807 : ∀ X0 X1 : G, (σ (M.op (τ X1) X0)) ≠ X1 ∨ (M.op X0 X0) = (τ X1) ∨ (k X1 (σ X0)) = X1 ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14792 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq14792
    | (have j0 := eq14792 X0 X1
       grind)
    | exact resolve eq14792 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14792
  have eq15072 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14807 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14807
    | (have j0 := eq14807 X1 (σ X0)
       grind)
    | exact resolve eq14807 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807
  have eq15111 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (σ X1)))) ∨ (σ X0) ≠ (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15072 X0 X1
       have i₂ := eq20 (σ X1) X0
       grind)
    | exact superpose eq20 eq15072
    | (have j0 := eq15072 X0 X1
       grind)
    | exact resolve eq15072 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15072
  have eq15125 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) ≠ (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15111 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq15111
    | (have j0 := eq15111 X0 X1
       grind)
    | exact resolve eq15111 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15111
  have eq15138 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) ≠ (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15125 X0 X1
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq15125
    | (have j0 := eq15125 X0 X1
       grind)
    | exact resolve eq15125 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq15125
  have eq15147 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15138 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq15138
    | (have j0 := eq15138 X0 X1
       grind)
    | exact resolve eq15138 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15138
  have eq24753 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15147 x y
       have i₂ := eq3630
       grind)
    | exact superpose eq3630 eq15147
    | (have j0 := eq15147 x y
       grind)
    | (have r₁ := eq15147 x y
       have r₂ := eq3630
       grind)
    | exact resolve eq15147 eq3630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630
  have eq24760 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24753
  have eq24761 : (σ x) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24760
  have eq24768 : (σ x) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq15147 x y
       grind)
    | (have r₁ := eq24761
       have r₂ := eq15147 x y
       grind)
    | exact resolve eq24761 eq15147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15147 eq24761
  have eq24769 : x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have j1 := eq593 x y
       grind)
    | (have r₁ := eq24768
       have r₂ := eq593 x y
       grind)
    | exact resolve eq24768 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq24768
  have eq79431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq24769
       grind)
    | exact superpose eq24769 eq410
    | exact resolve eq410 eq24769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24769
  have eq79505 : y = (M.op x x) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq79431
       have r₂ := eq16
       grind)
    | exact resolve eq79431 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79431
  have eq79854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq409 x
       have i₂ := eq79505
       grind)
    | exact superpose eq79505 eq409
    | exact resolve eq409 eq79505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79505
  have eq79929 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq79854
       have r₂ := eq16
       grind)
    | exact resolve eq79854 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79854
  have eq80613 : (M.op y y) = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq79929
       grind)
    | exact superpose eq79929 eq9
    | exact resolve eq9 eq79929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79929
  have eq80707 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq80613
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq80613
    | exact resolve eq80613 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80613
  have eq81369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq80707
       grind)
    | exact superpose eq80707 eq410
    | exact resolve eq410 eq80707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80707
  have eq81443 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq81369
       have r₂ := eq16
       grind)
    | exact resolve eq81369 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81369
  have eq82003 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq81443
       grind)
    | exact superpose eq81443 eq9
    | exact resolve eq9 eq81443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81443
  have eq82097 : y = (M.op x x) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq82003
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq82003
    | exact resolve eq82003 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82003
  have eq82655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq409 x
       have i₂ := eq82097
       grind)
    | exact superpose eq82097 eq409
    | exact resolve eq409 eq82097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82097
  have eq82730 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq82655
       have r₂ := eq16
       grind)
    | exact resolve eq82655 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82655
  have eq84232 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq82730
       grind)
    | exact superpose eq82730 eq9
    | exact resolve eq9 eq82730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82730
  have eq84370 : x = (k x y) := by
    first
    | (have i₁ := eq84232
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq84232
    | exact resolve eq84232 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84232
  have eq84685 : (σ y) = (σ (M.op x x)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3673
       have i₂ := eq84370
       grind)
    | exact superpose eq84370 eq3673
    | exact resolve eq3673 eq84370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq87446 : (τ (σ y)) = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq84685
       grind)
    | exact superpose eq84685 eq9
    | exact resolve eq9 eq84685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84685
  have eq87544 : y = (M.op x x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq87446
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq87446
    | exact resolve eq87446 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87446
  have eq88035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq409 x
       have i₂ := eq87544
       grind)
    | exact superpose eq87544 eq409
    | exact resolve eq409 eq87544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87544
  have eq88110 : (σ x) = (σ (M.op y y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq88035
       have r₂ := eq16
       grind)
    | exact resolve eq88035 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88035
  have eq89146 : (M.op y y) = (τ (σ x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq88110
       grind)
    | exact superpose eq88110 eq9
    | exact resolve eq9 eq88110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88110
  have eq89246 : x = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq89146
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq89146
    | exact resolve eq89146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89146
  have eq89595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq89246
       grind)
    | exact superpose eq89246 eq410
    | exact resolve eq410 eq89246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89246
  have eq89669 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq89595
       have r₂ := eq16
       grind)
    | exact resolve eq89595 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89595
  have eq90730 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq89669
       grind)
    | exact superpose eq89669 eq10
    | exact resolve eq10 eq89669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89669
  have eq90964 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90730
       grind)
    | exact superpose eq90730 eq16
    | exact resolve eq16 eq90730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93347 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90964
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq90964
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq90964 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93352 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq93347
  have eq93353 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93352
       have i₂ := eq84370
       grind)
    | exact superpose eq84370 eq93352
    | exact resolve eq93352 eq84370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84370 eq93352
  have eq93609 : (σ x) ≠ (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90964
       have i₂ := eq93353
       grind)
    | exact superpose eq93353 eq90964
    | exact resolve eq90964 eq93353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93353
  have eq93650 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq93609
  have eq93657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq409 x
       have i₂ := eq93650
       grind)
    | exact superpose eq93650 eq409
    | exact resolve eq409 eq93650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq93650
  have eq93732 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93657
       have i₂ := eq90730
       grind)
    | exact superpose eq90730 eq93657
    | exact resolve eq93657 eq90730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93657
  have eq93746 : x = (M.op y y) := by
    first
    | (have r₁ := eq93732
       have r₂ := eq90964
       grind)
    | exact resolve eq93732 eq90964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93732
  have eq93858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq93746
       grind)
    | exact superpose eq93746 eq410
    | exact resolve eq410 eq93746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq93746
  have eq93932 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq93858
       have i₂ := eq90730
       grind)
    | exact superpose eq90730 eq93858
    | exact resolve eq93858 eq90730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90730 eq93858
  have eq93948 : False := by grind
  exact eq93948

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X) else if m(X,Y) = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_pxy_y_pyx_pyx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq32 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq40 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq43 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq45 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq50 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq54 : (M.op (σ x) (σ y)) = (σ (k x (τ (σ y)))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq40
       have i₂ := eq20 (σ y) x
       grind)
    | exact superpose eq20 eq40
    | exact resolve eq40 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq55 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq47 (τ X0)
       grind)
    | exact superpose eq47 eq23
    | (have j1 := eq47 (τ X0)
       grind)
    | exact resolve eq23 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq60 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | (have j0 := eq59 X0
       grind)
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 (σ X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq51
    | (have j0 := eq51 X1 (σ X0)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (τ X0)
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X1 (τ X0)
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq95 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq55
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq55
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq95
  have eq108 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | (have j0 := eq64 X1 (σ X0)
       grind)
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq162 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq60
  have eq163 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq162 X0
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq162
    | (have j0 := eq162 X0
       grind)
    | exact resolve eq162 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq166 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq163 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163
    | (have j0 := eq163 X0
       grind)
    | exact resolve eq163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq167 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq193 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (τ (σ (k X0 (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq167 (σ X0)
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq167
    | exact resolve eq167 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq210 : ∀ X0 : G, (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq193 X0
       have i₂ := eq9 (k X0 (τ (σ X0)))
       grind)
    | exact superpose eq9 eq193
    | exact resolve eq193 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq217 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq210 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq210
    | exact resolve eq210 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq263 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq217 (σ X0)
       grind)
    | exact superpose eq217 eq20
    | exact resolve eq20 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq217 (τ X0)
       grind)
    | exact superpose eq217 eq23
    | exact resolve eq23 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq265 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq264 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq264
    | exact resolve eq264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq266 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq263 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq263
    | exact resolve eq263 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq270 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq265 X0
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq265
    | exact resolve eq265 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq271 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq266
    | exact resolve eq266 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq266
  have eq274 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq288 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq271 X1
       grind)
    | exact superpose eq271 eq108
    | (have j0 := eq108 X0 X1
       grind)
    | exact resolve eq108 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq303 : (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq271 x
       grind)
    | exact superpose eq271 eq96
    | exact resolve eq96 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq304 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq271 x
       grind)
    | exact superpose eq271 eq55
    | exact resolve eq55 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq312 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq304
       have i₂ := eq271 y
       grind)
    | exact superpose eq271 eq304
    | exact resolve eq304 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq313 : (M.op x y) = (k x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq303
       have i₂ := eq271 y
       grind)
    | exact superpose eq271 eq303
    | exact resolve eq303 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq318 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq288
    | (have j0 := eq288 X0 X1
       grind)
    | exact resolve eq288 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq404 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 (σ X0)
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq35
    | exact resolve eq35 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq412 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq405 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq405
    | exact resolve eq405 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq413 : ∀ X0 : G, (σ (k X0 (τ (σ (M.op X0 X0))))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq404 X0
       have i₂ := eq20 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq20 eq404
    | exact resolve eq404 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq416 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq412
    | exact resolve eq412 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq417 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq413 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq413
    | exact resolve eq413 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq418 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq416
  have eq419 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq417 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq417
    | exact resolve eq417 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq417
  have eq476 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (σ X1))
       have i₂ := eq274 X0 X1
       grind)
    | exact superpose eq274 eq10
    | (have j1 := eq274 X0 X1
       grind)
    | exact resolve eq10 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq318 y x
       have i₂ := eq313
       grind)
    | exact superpose eq313 eq318
    | (have j0 := eq318 y x
       grind)
    | exact resolve eq318 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq318
  have eq602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq591
  have eq604 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq602
       have r₂ := eq16
       grind)
    | exact resolve eq602 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq608 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq604
       have r₂ := eq312
       grind)
    | exact resolve eq604 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq604
  have eq1446 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq476
    | (have j0 := eq476 X1 (τ X0)
       grind)
    | exact resolve eq476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq1484 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1446 X0 X1
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq1446
    | (have j0 := eq1446 X0 X1
       grind)
    | exact resolve eq1446 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq1446
  have eq2173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq418 x
       have i₂ := eq608
       grind)
    | exact superpose eq608 eq418
    | exact resolve eq418 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq2193 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2173
       have r₂ := eq16
       grind)
    | exact resolve eq2173 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq3544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq419 y
       have i₂ := eq2193
       grind)
    | exact superpose eq2193 eq419
    | exact resolve eq419 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq3566 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq3544
       have r₂ := eq16
       grind)
    | exact resolve eq3544 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq13909 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1484 X0 X1
       grind)
    | exact superpose eq1484 eq10
    | (have j1 := eq1484 X0 X1
       grind)
    | exact resolve eq10 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq13962 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13909 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13909
    | (have j0 := eq13909 X0 X1
       grind)
    | exact resolve eq13909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq15759 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13962 X0 (σ X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq13962
    | (have j0 := eq13962 X1 (σ X0)
       grind)
    | exact resolve eq13962 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13962
  have eq15928 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15759 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15759
    | (have j0 := eq15759 X0 X1
       grind)
    | exact resolve eq15759 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15759
  have eq15978 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15928 X0 X1
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq15928
    | (have j0 := eq15928 X0 X1
       grind)
    | exact resolve eq15928 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15928
  have eq16009 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15978 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq15978
    | (have j0 := eq15978 X0 X1
       grind)
    | exact resolve eq15978 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq16032 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16009 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16009
    | (have j0 := eq16009 X0 X1
       grind)
    | exact resolve eq16009 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16009
  have eq19965 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16032 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16032
    | (have j0 := eq16032 X1 (σ X0)
       grind)
    | exact resolve eq16032 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16032
  have eq20131 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19965 X0 X1
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq19965
    | (have j0 := eq19965 X0 X1
       grind)
    | exact resolve eq19965 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq19965
  have eq20142 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20131 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq20131
    | (have j0 := eq20131 X0 X1
       grind)
    | exact resolve eq20131 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20131
  have eq20558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq3566
       have i₂ := eq20142 y x
       grind)
    | exact superpose eq20142 eq3566
    | (have j1 := eq20142 y x
       grind)
    | exact resolve eq3566 eq20142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20142
  have eq20625 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq20558
       have r₂ := eq16
       grind)
    | exact resolve eq20558 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20558
  have eq91230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq418 x
       have i₂ := eq20625
       grind)
    | exact superpose eq20625 eq418
    | exact resolve eq418 eq20625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20625
  have eq91286 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq91230
       have r₂ := eq16
       grind)
    | exact resolve eq91230 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91230
  have eq91511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq419 y
       have i₂ := eq91286
       grind)
    | exact superpose eq91286 eq419
    | exact resolve eq419 eq91286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91286
  have eq91572 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq91511
       have r₂ := eq16
       grind)
    | exact resolve eq91511 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91511
  have eq91719 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq91572
       grind)
    | exact superpose eq91572 eq9
    | exact resolve eq9 eq91572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91572
  have eq91780 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq91719
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq91719
    | exact resolve eq91719 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91719
  have eq92129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq418 x
       have i₂ := eq91780
       grind)
    | exact superpose eq91780 eq418
    | exact resolve eq418 eq91780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91780
  have eq92193 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq92129
       have r₂ := eq16
       grind)
    | exact resolve eq92129 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92129
  have eq92560 : (M.op y y) = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq92193
       grind)
    | exact superpose eq92193 eq9
    | exact resolve eq9 eq92193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92193
  have eq92626 : x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq92560
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq92560
    | exact resolve eq92560 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92560
  have eq93080 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq419 y
       have i₂ := eq92626
       grind)
    | exact superpose eq92626 eq419
    | exact resolve eq419 eq92626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92626
  have eq93143 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq93080
       have r₂ := eq16
       grind)
    | exact resolve eq93080 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93080
  have eq93196 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3566
       have i₂ := eq93143
       grind)
    | exact superpose eq93143 eq3566
    | exact resolve eq3566 eq93143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq94014 : (τ (σ y)) = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq93143
       grind)
    | exact superpose eq93143 eq9
    | exact resolve eq9 eq93143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93143
  have eq94153 : y = (k x y) := by
    first
    | (have i₁ := eq94014
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq94014
    | exact resolve eq94014 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94014
  have eq96640 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq93196
       grind)
    | exact superpose eq93196 eq16
    | exact resolve eq16 eq93196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93196
  have eq97297 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96640
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq96640
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq96640 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97304 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq97297
  have eq97305 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97304
       have i₂ := eq94153
       grind)
    | exact superpose eq94153 eq97304
    | exact resolve eq97304 eq94153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94153 eq97304
  have eq97822 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96640
       have i₂ := eq97305
       grind)
    | exact superpose eq97305 eq96640
    | exact resolve eq96640 eq97305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96640 eq97305
  have eq97856 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq97822
  have eq97857 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq97856
  have eq98245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq418 x
       have i₂ := eq97857
       grind)
    | exact superpose eq97857 eq418
    | exact resolve eq418 eq97857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97857
  have eq98309 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq98245
       have r₂ := eq16
       grind)
    | exact resolve eq98245 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98245
  have eq98649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq419 y
       have i₂ := eq98309
       grind)
    | exact superpose eq98309 eq419
    | exact resolve eq419 eq98309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98309
  have eq98712 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq98649
       have r₂ := eq16
       grind)
    | exact resolve eq98649 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98649
  have eq98897 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq98712
       grind)
    | exact superpose eq98712 eq9
    | exact resolve eq9 eq98712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98712
  have eq99005 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq98897
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq98897
    | exact resolve eq98897 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98897
  have eq99194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq418 x
       have i₂ := eq99005
       grind)
    | exact superpose eq99005 eq418
    | exact resolve eq418 eq99005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq99005
  have eq99258 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq99194
       have r₂ := eq16
       grind)
    | exact resolve eq99194 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99194
  have eq99815 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq419 y
       have i₂ := eq99258
       grind)
    | exact superpose eq99258 eq419
    | exact resolve eq419 eq99258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq99829 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq99258
       grind)
    | exact superpose eq99258 eq9
    | exact resolve eq9 eq99258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99258
  have eq99967 : x = (M.op y y) := by
    first
    | (have i₁ := eq99829
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq99829
    | exact resolve eq99829 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99829
  have eq100313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99815
       have i₂ := eq99967
       grind)
    | exact superpose eq99967 eq99815
    | exact resolve eq99815 eq99967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99815 eq99967
  have eq100470 : False := by grind
  exact eq100470

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y) else if m(Y,X) = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_pyx_y_pxy_pxy_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq32 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq40 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq43 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq45 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq50 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq54 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40
       have i₂ := eq20 (σ x) y
       grind)
    | exact superpose eq20 eq40
    | exact resolve eq40 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq55 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq47 (τ X0)
       grind)
    | exact superpose eq47 eq23
    | (have j1 := eq47 (τ X0)
       grind)
    | exact resolve eq23 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq60 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | (have j0 := eq59 X0
       grind)
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) (σ X0)) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 (σ X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq51
    | (have j0 := eq51 X1 (σ X0)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (τ X0)
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X1 (τ X0)
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq95 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq55
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq55
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq95
  have eq108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq64
    | (have j0 := eq64 X1 (σ X0)
       grind)
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq162 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq60
  have eq163 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq162 X0
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq162
    | (have j0 := eq162 X0
       grind)
    | exact resolve eq162 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq166 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq163 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq163
    | (have j0 := eq163 X0
       grind)
    | exact resolve eq163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq167 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq193 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (τ (σ (k X0 (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq167 (σ X0)
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq167
    | exact resolve eq167 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq210 : ∀ X0 : G, (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq193 X0
       have i₂ := eq9 (k X0 (τ (σ X0)))
       grind)
    | exact superpose eq9 eq193
    | exact resolve eq193 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq217 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq210 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq210
    | exact resolve eq210 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq263 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq217 (σ X0)
       grind)
    | exact superpose eq217 eq20
    | exact resolve eq20 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq217 (τ X0)
       grind)
    | exact superpose eq217 eq23
    | exact resolve eq23 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq265 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq264 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq264
    | exact resolve eq264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq266 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq263 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq263
    | exact resolve eq263 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq270 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq265 X0
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq265
    | exact resolve eq265 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq271 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq266 X0
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq266
    | exact resolve eq266 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq266
  have eq274 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq288 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq271 X1
       grind)
    | exact superpose eq271 eq108
    | (have j0 := eq108 X0 X1
       grind)
    | exact resolve eq108 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq303 : (σ y) = (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq271 x
       grind)
    | exact superpose eq271 eq96
    | exact resolve eq96 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq304 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq271 x
       grind)
    | exact superpose eq271 eq55
    | exact resolve eq55 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq312 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq304
       have i₂ := eq271 y
       grind)
    | exact superpose eq271 eq304
    | exact resolve eq304 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq313 : (M.op x y) = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq303
       have i₂ := eq271 y
       grind)
    | exact superpose eq271 eq303
    | exact resolve eq303 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq318 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq288
    | (have j0 := eq288 X0 X1
       grind)
    | exact resolve eq288 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq404 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (σ X0)
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq35
    | exact resolve eq35 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq412 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq405 X0
       have i₂ := eq20 (σ X0) (M.op X0 X0)
       grind)
    | exact superpose eq20 eq405
    | exact resolve eq405 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq413 : ∀ X0 : G, (σ (k X0 (τ (σ (M.op X0 X0))))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq404 X0
       have i₂ := eq20 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq20 eq404
    | exact resolve eq404 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq416 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq412
    | exact resolve eq412 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq417 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq413 X0
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq413
    | exact resolve eq413 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq418 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq416
  have eq419 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq417 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq417
    | exact resolve eq417 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq417
  have eq476 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (τ X1) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq10
    | (have j1 := eq274 X1 X0
       grind)
    | exact resolve eq10 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq318 x y
       have i₂ := eq313
       grind)
    | exact superpose eq313 eq318
    | (have j0 := eq318 x y
       grind)
    | exact resolve eq318 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq318
  have eq602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq591
  have eq604 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq602
       have r₂ := eq16
       grind)
    | exact resolve eq602 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq608 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq604
       have r₂ := eq312
       grind)
    | exact resolve eq604 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq604
  have eq1446 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq476 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq476
    | (have j0 := eq476 (τ X0) X1
       grind)
    | exact resolve eq476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq1484 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1446 X0 X1
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq1446
    | (have j0 := eq1446 X0 X1
       grind)
    | exact resolve eq1446 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq1446
  have eq2174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq419 x
       have i₂ := eq608
       grind)
    | exact superpose eq608 eq419
    | exact resolve eq419 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq2193 : x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2174
       have r₂ := eq16
       grind)
    | exact resolve eq2174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq3543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq418 y
       have i₂ := eq2193
       grind)
    | exact superpose eq2193 eq418
    | exact resolve eq418 eq2193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq3566 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq3543
       have r₂ := eq16
       grind)
    | exact resolve eq3543 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3543
  have eq14130 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1484 X0 X1
       grind)
    | exact superpose eq1484 eq10
    | (have j1 := eq1484 X0 X1
       grind)
    | exact resolve eq10 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq14183 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14130 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14130
    | (have j0 := eq14130 X0 X1
       grind)
    | exact resolve eq14130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14130
  have eq16192 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) (τ (σ X0)))) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14183 X0 (σ X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq14183
    | (have j0 := eq14183 X1 (σ X0)
       grind)
    | exact resolve eq14183 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14183
  have eq16362 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16192 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16192
    | (have j0 := eq16192 X0 X1
       grind)
    | exact resolve eq16192 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16192
  have eq16412 : ∀ X0 X1 : G, (τ X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16362 X0 X1
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq16362
    | (have j0 := eq16362 X0 X1
       grind)
    | exact resolve eq16362 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16362
  have eq16443 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (σ (k X0 (τ X1))) = X1 ∨ (τ (σ X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16412 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq16412
    | (have j0 := eq16412 X0 X1
       grind)
    | exact resolve eq16412 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16412
  have eq16466 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 X0) = (τ X1) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ (k X0 (τ X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16443 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16443
    | (have j0 := eq16443 X0 X1
       grind)
    | exact resolve eq16443 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16443
  have eq20596 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16466 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16466
    | (have j0 := eq16466 X1 (σ X0)
       grind)
    | exact resolve eq16466 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16466
  have eq20763 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20596 X0 X1
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq20596
    | (have j0 := eq20596 X0 X1
       grind)
    | exact resolve eq20596 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq20596
  have eq20775 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20763 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq20763
    | (have j0 := eq20763 X0 X1
       grind)
    | exact resolve eq20763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20763
  have eq21275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq3566
       have i₂ := eq20775 x y
       grind)
    | exact superpose eq20775 eq3566
    | (have j1 := eq20775 x y
       grind)
    | exact resolve eq3566 eq20775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20775
  have eq21340 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq21275
       have r₂ := eq16
       grind)
    | exact resolve eq21275 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21275
  have eq90885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq418 y
       have i₂ := eq21340
       grind)
    | exact superpose eq21340 eq418
    | exact resolve eq418 eq21340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21340
  have eq90941 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq90885
       have r₂ := eq16
       grind)
    | exact resolve eq90885 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90885
  have eq91359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq419 x
       have i₂ := eq90941
       grind)
    | exact superpose eq90941 eq419
    | exact resolve eq419 eq90941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90941
  have eq91420 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq91359
       have r₂ := eq16
       grind)
    | exact resolve eq91359 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91359
  have eq91784 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq91420
       grind)
    | exact superpose eq91420 eq9
    | exact resolve eq9 eq91420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91420
  have eq91845 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq91784
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq91784
    | exact resolve eq91784 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91784
  have eq92031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq419 x
       have i₂ := eq91845
       grind)
    | exact superpose eq91845 eq419
    | exact resolve eq419 eq91845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91845
  have eq92094 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq92031
       have r₂ := eq16
       grind)
    | exact resolve eq92031 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92031
  have eq92286 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq92094
       grind)
    | exact superpose eq92094 eq9
    | exact resolve eq9 eq92094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92094
  have eq92354 : x = (M.op y y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq92286
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq92286
    | exact resolve eq92286 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92286
  have eq92697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq418 y
       have i₂ := eq92354
       grind)
    | exact superpose eq92354 eq418
    | exact resolve eq418 eq92354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92354
  have eq92761 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq92697
       have r₂ := eq16
       grind)
    | exact resolve eq92697 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92697
  have eq92814 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3566
       have i₂ := eq92761
       grind)
    | exact superpose eq92761 eq3566
    | exact resolve eq3566 eq92761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566
  have eq93586 : (τ (σ x)) = (k y x) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq92761
       grind)
    | exact superpose eq92761 eq9
    | exact resolve eq9 eq92761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92761
  have eq93794 : x = (k y x) := by
    first
    | (have i₁ := eq93586
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq93586
    | exact resolve eq93586 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93586
  have eq100591 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92814
       grind)
    | exact superpose eq92814 eq16
    | exact resolve eq16 eq92814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92814
  have eq101185 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100591
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq100591
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq100591 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101192 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq101185
  have eq101193 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101192
       have i₂ := eq93794
       grind)
    | exact superpose eq93794 eq101192
    | exact resolve eq101192 eq93794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93794 eq101192
  have eq197473 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100591
       have i₂ := eq101193
       grind)
    | exact superpose eq101193 eq100591
    | exact resolve eq100591 eq101193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100591 eq101193
  have eq197486 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq197473
  have eq197487 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq197486
  have eq197757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq418 y
       have i₂ := eq197487
       grind)
    | exact superpose eq197487 eq418
    | exact resolve eq418 eq197487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197487
  have eq197854 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq197757
       have r₂ := eq16
       grind)
    | exact resolve eq197757 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197757
  have eq198338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq419 x
       have i₂ := eq197854
       grind)
    | exact superpose eq197854 eq419
    | exact resolve eq419 eq197854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197854
  have eq198472 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq198338
       have r₂ := eq16
       grind)
    | exact resolve eq198338 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198338
  have eq198909 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq198472
       grind)
    | exact superpose eq198472 eq9
    | exact resolve eq9 eq198472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198472
  have eq198993 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq198909
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq198909
    | exact resolve eq198909 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198909
  have eq199788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq419 x
       have i₂ := eq198993
       grind)
    | exact superpose eq198993 eq419
    | exact resolve eq419 eq198993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq198993
  have eq199939 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq199788
       have r₂ := eq16
       grind)
    | exact resolve eq199788 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199788
  have eq200742 : (M.op (σ x) (σ y)) = (σ (M.op (M.op y y) y)) := by
    first
    | (have i₁ := eq418 y
       have i₂ := eq199939
       grind)
    | exact superpose eq199939 eq418
    | exact resolve eq418 eq199939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq200761 : (τ (σ x)) = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq199939
       grind)
    | exact superpose eq199939 eq9
    | exact resolve eq9 eq199939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199939
  have eq200899 : x = (M.op y y) := by
    first
    | (have i₁ := eq200761
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq200761
    | exact resolve eq200761 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200761
  have eq200973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq200742
       have i₂ := eq200899
       grind)
    | exact superpose eq200899 eq200742
    | exact resolve eq200742 eq200899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200742 eq200899
  have eq201083 : False := by grind
  exact eq201083

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y) else if X = Y then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_x_y_pxy_pxy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq20
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq75
    | exact resolve eq75 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq98 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq99 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq99
  have eq691 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq699 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq708 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq699
  have eq716 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq691
    | (have j0 := eq691 X0 X1
       grind)
    | exact resolve eq691 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq730 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq737 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq743 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq753 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq743 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq743
    | exact resolve eq743 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq753 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq753
    | exact resolve eq753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq784 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq774 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq774
    | exact resolve eq774 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq774
  have eq890 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730 x y
       grind)
    | exact superpose eq730 eq16
    | (have j1 := eq730 x y
       grind)
    | exact resolve eq16 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq10376 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq708
    | (have j0 := eq708 X1 (σ X0)
       grind)
    | exact resolve eq708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq10514 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10376 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10376
    | (have j0 := eq10376 X0 X1
       grind)
    | exact resolve eq10376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376
  have eq10527 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10514 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq10514
    | (have j0 := eq10514 X0 X1
       grind)
    | exact resolve eq10514 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10514
  have eq10535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10527 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10527
    | (have j0 := eq10527 X0 X1
       grind)
    | exact resolve eq10527 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq16862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq890
       have i₂ := eq10535 y x
       grind)
    | exact superpose eq10535 eq890
    | (have j1 := eq10535 y x
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 y x
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq890 eq10535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq10535
  have eq16863 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by grind
  clear eq16862
  have eq1774130 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16863
       grind)
    | exact superpose eq16863 eq16
    | exact resolve eq16 eq16863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16863
  have eq1774149 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774130
       have r₂ := eq80 x
       grind)
    | exact resolve eq1774130 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774130
  have eq1774227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq784 x
       have i₂ := eq1774149
       grind)
    | exact superpose eq1774149 eq784
    | exact resolve eq784 eq1774149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774149
  have eq1774387 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774227
       have r₂ := eq16
       grind)
    | exact resolve eq1774227 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774227
  have eq1774460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1774387
       grind)
    | exact superpose eq1774387 eq102
    | exact resolve eq102 eq1774387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774387
  have eq1774637 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774460
       have r₂ := eq16
       grind)
    | exact resolve eq1774460 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774460
  have eq1774655 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq1774637
       grind)
    | exact superpose eq1774637 eq9
    | exact resolve eq9 eq1774637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774637
  have eq1775197 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1774655
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1774655
    | exact resolve eq1774655 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774655
  have eq1775200 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1775197
       grind)
    | exact superpose eq1775197 eq16
    | exact resolve eq16 eq1775197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775197
  have eq1775219 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775200
       have r₂ := eq80 x
       grind)
    | exact resolve eq1775200 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1775200
  have eq1775440 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1775219
       grind)
    | exact superpose eq1775219 eq9
    | exact resolve eq9 eq1775219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775219
  have eq1776063 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1775440
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1775440
    | exact resolve eq1775440 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775440
  have eq1776155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq784 x
       have i₂ := eq1776063
       grind)
    | exact superpose eq1776063 eq784
    | exact resolve eq784 eq1776063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1776063
  have eq1776313 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1776155
       have r₂ := eq16
       grind)
    | exact resolve eq1776155 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776155
  have eq1776544 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1776313
       grind)
    | exact superpose eq1776313 eq9
    | exact resolve eq9 eq1776313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776313
  have eq1777167 : x = (M.op y y) := by
    first
    | (have i₁ := eq1776544
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1776544
    | exact resolve eq1776544 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776544
  have eq1777394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1777167
       grind)
    | exact superpose eq1777167 eq102
    | exact resolve eq102 eq1777167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1777167
  have eq1777569 : False := by grind
  exact eq1777569

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y) else if X = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pxx_y_x_y_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq20
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq75
    | exact resolve eq75 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq98 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq99 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq99
  have eq691 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq699 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq708 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq699
  have eq716 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq691
    | (have j0 := eq691 X0 X1
       grind)
    | exact resolve eq691 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq730 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq737 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq743 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq753 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq743 (σ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq743
    | exact resolve eq743 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq753 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq753
    | exact resolve eq753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq784 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq774 X0
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq774
    | exact resolve eq774 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq774
  have eq890 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730 x y
       grind)
    | exact superpose eq730 eq16
    | (have j1 := eq730 x y
       grind)
    | exact resolve eq16 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq10376 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq708
    | (have j0 := eq708 X1 (σ X0)
       grind)
    | exact resolve eq708 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq10514 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10376 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10376
    | (have j0 := eq10376 X0 X1
       grind)
    | exact resolve eq10376 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10376
  have eq10527 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10514 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq10514
    | (have j0 := eq10514 X0 X1
       grind)
    | exact resolve eq10514 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10514
  have eq10535 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10527 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10527
    | (have j0 := eq10527 X0 X1
       grind)
    | exact resolve eq10527 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq16862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq890
       have i₂ := eq10535 y x
       grind)
    | exact superpose eq10535 eq890
    | (have j1 := eq10535 y x
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 y x
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq890
       have r₂ := eq10535 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq890 eq10535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq10535
  have eq16863 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by grind
  clear eq16862
  have eq1774130 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16863
       grind)
    | exact superpose eq16863 eq16
    | exact resolve eq16 eq16863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16863
  have eq1774149 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774130
       have r₂ := eq80 x
       grind)
    | exact resolve eq1774130 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774130
  have eq1774227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq784 x
       have i₂ := eq1774149
       grind)
    | exact superpose eq1774149 eq784
    | exact resolve eq784 eq1774149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774149
  have eq1774387 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774227
       have r₂ := eq16
       grind)
    | exact resolve eq1774227 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774227
  have eq1774460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1774387
       grind)
    | exact superpose eq1774387 eq102
    | exact resolve eq102 eq1774387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774387
  have eq1774637 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1774460
       have r₂ := eq16
       grind)
    | exact resolve eq1774460 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774460
  have eq1774655 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq1774637
       grind)
    | exact superpose eq1774637 eq9
    | exact resolve eq9 eq1774637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774637
  have eq1775197 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1774655
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1774655
    | exact resolve eq1774655 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774655
  have eq1775200 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1775197
       grind)
    | exact superpose eq1775197 eq16
    | exact resolve eq16 eq1775197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775197
  have eq1775219 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775200
       have r₂ := eq80 x
       grind)
    | exact resolve eq1775200 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1775200
  have eq1775440 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1775219
       grind)
    | exact superpose eq1775219 eq9
    | exact resolve eq9 eq1775219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775219
  have eq1776063 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1775440
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1775440
    | exact resolve eq1775440 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775440
  have eq1776155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq784 x
       have i₂ := eq1776063
       grind)
    | exact superpose eq1776063 eq784
    | exact resolve eq784 eq1776063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1776063
  have eq1776313 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1776155
       have r₂ := eq16
       grind)
    | exact resolve eq1776155 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776155
  have eq1776544 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1776313
       grind)
    | exact superpose eq1776313 eq9
    | exact resolve eq9 eq1776313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776313
  have eq1777167 : x = (M.op y y) := by
    first
    | (have i₁ := eq1776544
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1776544
    | exact resolve eq1776544 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776544
  have eq1777394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1777167
       grind)
    | exact superpose eq1777167 eq102
    | exact resolve eq102 eq1777167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1777167
  have eq1777569 : False := by grind
  exact eq1777569
