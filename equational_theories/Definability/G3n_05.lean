import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pyy_x_pxx_y_pxy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : x = (τ (σ x)) := by
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
  have eq33 : y = (τ (σ y)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq46 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k x X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq61 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 x)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq16
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 y)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq46 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46
    | (have j0 := eq46 x
       grind)
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq117 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq49 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq49
    | (have j0 := eq49 y
       grind)
    | exact resolve eq49 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq143 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq61 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq61
    | exact resolve eq61 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq154 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq74 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq74
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq18
    | (have j1 := eq29 x y
       grind)
    | exact resolve eq18 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq29 sF2 sF3
       grind)
    | exact superpose eq29 eq26
    | (have j1 := eq29 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq193 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq176 sF2
       grind)
    | exact superpose eq176 eq180
    | exact resolve eq180 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq194 : y = (k x x) ∨ (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq179
       have i₂ := eq176 x
       grind)
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq199 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq193
       have i₂ := eq176 sF3
       grind)
    | exact superpose eq176 eq193
    | exact resolve eq193 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq200 : (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq194
       have i₂ := eq176 y
       grind)
    | exact superpose eq176 eq194
    | exact resolve eq194 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq204 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq176 X1
       grind)
    | exact superpose eq176 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | (have r₁ := eq204 X0 X0
       have r₂ := eq176 X0
       grind)
    | exact resolve eq204 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1104 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1104 X0
       have i₂ := eq176 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq1104
    | (have j0 := eq1104 X0
       grind)
    | exact resolve eq1104 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1109 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1106 X0
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq1106
    | (have j0 := eq1106 X0
       grind)
    | exact resolve eq1106 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1110 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1109 X0
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq1109
    | (have j0 := eq1109 X0
       grind)
    | exact resolve eq1109 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1113 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1115 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1113 X0
       have i₂ := eq176 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq1113
    | (have j0 := eq1113 X0
       grind)
    | exact resolve eq1113 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1118 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1115 X0
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq1115
    | (have j0 := eq1115 X0
       grind)
    | exact resolve eq1115 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1119 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1118 X0
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq1118
    | (have j0 := eq1118 X0
       grind)
    | exact resolve eq1118 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq1118
  have eq3553 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq200
       grind)
    | exact superpose eq200 eq42
    | exact resolve eq42 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq3554 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq3553
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3553
    | exact resolve eq3553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq3557 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq3554
    | exact resolve eq3554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq14243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq3557 eq199
    | exact resolve eq199 eq3557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq3557
  have eq14250 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have r₁ := eq14243
       have r₂ := eq27
       grind)
    | exact resolve eq14243 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14243
  have eq14258 : (τ (σ y)) = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq14250 eq99
    | exact resolve eq99 eq14250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq14250
  have eq14273 : y = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq33 eq14258
    | exact resolve eq14258 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14258
  have eq14274 : (σ x) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ x = (k y y) := by grind
  clear eq14273
  have eq14283 : (τ (σ x)) = (k y y) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq14274 eq117
    | exact resolve eq117 eq14274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq14274
  have eq14298 : x = (k y y) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | exact superpose eq31 eq14283
    | exact resolve eq14283 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14283
  have eq14299 : y = (k x x) ∨ x = (k y y) := by grind
  clear eq14298
  have eq14309 : (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq14299
       grind)
    | exact superpose eq14299 eq41
    | exact resolve eq41 eq14299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14314 : ∀ X0 : G, y ≠ (k X0 X0) ∨ (k x X0) = (M.op x X0) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq205 x X0
       have i₂ := eq14299
       grind)
    | exact superpose eq14299 eq205
    | (have j0 := eq205 x X0
       grind)
    | exact resolve eq205 eq14299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14316 : (M.op x y) = (k y x) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1110 x
       have i₂ := eq14299
       grind)
    | exact superpose eq14299 eq1110
    | exact resolve eq1110 eq14299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14299
  have eq14318 : (M.op x y) = (k y x) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14316
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14316
    | exact resolve eq14316 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14316
  have eq14319 : (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14309
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14309
    | exact resolve eq14309 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14309
  have eq14323 : (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14319
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14319
    | exact resolve eq14319 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14319
  have eq14334 : ∀ X0 : G, (σ y) ≠ (k X0 X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq14323 eq205
    | (have j0 := eq205 (σ x) X0
       grind)
    | exact resolve eq205 eq14323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14336 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq14323 eq1110
    | exact resolve eq1110 eq14323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq14323
  have eq14338 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq14336
    | exact resolve eq14336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14336
  have eq14349 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq14318
       grind)
    | exact superpose eq14318 eq41
    | exact resolve eq41 eq14318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14318
  have eq14350 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14349
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14349
    | exact resolve eq14349 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14349
  have eq14354 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq14350
    | exact resolve eq14350 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14350
  have eq14366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq14354 eq14338
    | exact resolve eq14338 eq14354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14338 eq14354
  have eq14372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k y y) := by grind
  clear eq14366
  have eq14379 : (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (k y y) := by
    first
    | (have r₁ := eq14372
       have r₂ := eq27
       grind)
    | exact resolve eq14372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14372
  have eq14389 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq14379 eq154
    | exact resolve eq154 eq14379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq14379
  have eq14398 : y = (k y y) ∨ x = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq33 eq14389
    | exact resolve eq14389 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq14389
  have eq14399 : y = (k y y) ∨ x = (k y y) := by grind
  clear eq14398
  have eq14409 : (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq14399
       grind)
    | exact superpose eq14399 eq42
    | exact resolve eq42 eq14399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14416 : x ≠ y ∨ x = (k y y) := by grind
  have eq14417 : (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14409
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14409
    | exact resolve eq14409 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14409
  have eq14542 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq14314 y
       have i₂ := eq14399
       grind)
    | exact superpose eq14399 eq14314
    | (have j0 := eq14314 y
       grind)
    | (have r₁ := eq14314 y
       have r₂ := eq14399
       grind)
    | exact resolve eq14314 eq14399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14314 eq14399
  have eq14553 : (M.op x y) = (k x y) ∨ x = y ∨ x = (k y y) := by grind
  clear eq14542
  have eq14556 : (M.op x y) = (k x y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq14553
       have r₂ := eq14416
       grind)
    | exact resolve eq14553 eq14416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14416 eq14553
  have eq14558 : (M.op x y) = (k x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14556
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14556
    | exact resolve eq14556 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14556
  have eq14562 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq14558
       grind)
    | exact superpose eq14558 eq42
    | exact resolve eq42 eq14558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14558
  have eq14563 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14562
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14562
    | exact resolve eq14562 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14562
  have eq14567 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq14563
    | exact resolve eq14563 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14563
  have eq14734 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq14417 eq14334
    | (have j0 := eq14334 (σ y)
       grind)
    | (have r₁ := eq14334 (σ y)
       have r₂ := eq14417
       grind)
    | exact resolve eq14334 eq14417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14334 eq14417
  have eq14740 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq14734
  have eq14741 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq14740
  have eq14747 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq14741
    | exact resolve eq14741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14741
  have eq14750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq14567 eq14747
    | exact resolve eq14747 eq14567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14567 eq14747
  have eq14751 : x = (k y y) := by
    first
    | (have r₁ := eq14750
       have r₂ := eq27
       grind)
    | exact resolve eq14750 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14750
  have eq14911 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq14751
       grind)
    | exact superpose eq14751 eq42
    | exact resolve eq42 eq14751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14917 : ∀ X0 : G, x ≠ (k X0 X0) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq205 X0 y
       have i₂ := eq14751
       grind)
    | exact superpose eq14751 eq205
    | (have j0 := eq205 X0 y
       grind)
    | exact resolve eq205 eq14751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14921 : (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1119 y
       have i₂ := eq14751
       grind)
    | exact superpose eq14751 eq1119
    | exact resolve eq1119 eq14751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14751
  have eq14924 : (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14921
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14921
    | exact resolve eq14921 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14921
  have eq14925 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14911
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14911
    | exact resolve eq14911 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14911
  have eq14930 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14925
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14925
    | exact resolve eq14925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14925
  have eq14946 : ∀ X0 : G, (σ x) ≠ (k X0 X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq14930 eq205
    | (have j0 := eq205 X0 (σ y)
       grind)
    | exact resolve eq205 eq14930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq14950 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14930 eq1119
    | exact resolve eq1119 eq14930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq14930
  have eq14955 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq14950
    | exact resolve eq14950 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14950
  have eq14968 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq14924
       grind)
    | exact superpose eq14924 eq41
    | exact resolve eq41 eq14924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14924
  have eq14969 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14968
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14968
    | exact resolve eq14968 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14968
  have eq14973 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq14969
    | exact resolve eq14969 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14969
  have eq14992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq14973 eq14955
    | exact resolve eq14955 eq14973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14955 eq14973
  have eq14997 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq14992
       have r₂ := eq27
       grind)
    | exact resolve eq14992 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14992
  have eq15014 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) := by
    first
    | exact superpose eq14997 eq143
    | exact resolve eq143 eq14997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq14997
  have eq15027 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq31 eq15014
    | exact resolve eq15014 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15014
  have eq15028 : x = (k x x) := by grind
  clear eq15027
  have eq15040 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq15028
       grind)
    | exact superpose eq15028 eq41
    | exact resolve eq41 eq15028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq15054 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15040
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15040
    | exact resolve eq15040 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15040
  have eq15210 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq14917 x
       have i₂ := eq15028
       grind)
    | exact superpose eq15028 eq14917
    | (have j0 := eq14917 x
       grind)
    | (have r₁ := eq14917 x
       have r₂ := eq15028
       grind)
    | exact resolve eq14917 eq15028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14917 eq15028
  have eq15223 : (M.op x y) = (k x y) := by grind
  clear eq15210
  have eq15226 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq15223
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15223
    | exact resolve eq15223 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15223
  have eq15231 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq15226
       grind)
    | exact superpose eq15226 eq42
    | exact resolve eq42 eq15226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq15226
  have eq15232 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq15231
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15231
    | exact resolve eq15231 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15231
  have eq15236 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15232
    | exact resolve eq15232 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15232
  have eq15804 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq15054 eq14946
    | (have j0 := eq14946 (σ x)
       grind)
    | (have r₁ := eq14946 (σ x)
       have r₂ := eq15054
       grind)
    | exact resolve eq14946 eq15054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14946 eq15054
  have eq15815 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq15804
  have eq15818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15236 eq15815
    | exact resolve eq15815 eq15236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15236 eq15815
  have eq15821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15818 eq26
    | exact resolve eq26 eq15818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15818
  have eq15823 : False := by grind
  exact eq15823

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pyy_x_pxx_y_pyx_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq52 (σ X0)
       grind)
    | exact superpose eq52 eq10
    | exact resolve eq10 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq52 x
       grind)
    | exact superpose eq52 eq45
    | exact resolve eq45 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq56 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq52 sF2
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq67 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq51
       have i₂ := eq52 sF2
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq52 x
       grind)
    | exact superpose eq52 eq67
    | exact resolve eq67 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq38
  have eq98 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq52 sF3
       grind)
    | exact superpose eq52 eq94
    | exact resolve eq94 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq100 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq52 y
       grind)
    | exact superpose eq52 eq98
    | exact resolve eq98 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq93
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq93 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq108
    | exact resolve eq108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq120 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0 (τ X0)
       have i₂ := eq52 (τ X0)
       grind)
    | exact superpose eq52 eq36
    | exact resolve eq36 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq268 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq275 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq263 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq263
    | exact resolve eq263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq275
    | exact resolve eq275 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq275
  have eq342 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq40
  have eq528 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq558 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq268 X0 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq268
    | (have j0 := eq268 X0 x
       grind)
    | exact resolve eq268 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq631 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq16
    | exact resolve eq16 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq6121 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq631 X0
       grind)
    | exact superpose eq631 eq342
    | (have j0 := eq342 X0
       grind)
    | exact resolve eq342 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq6122 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6121 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq6121
    | (have j0 := eq6121 X0
       grind)
    | exact resolve eq6121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6121
  have eq6123 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6122 X0
       have i₂ := eq631 X0
       grind)
    | exact superpose eq631 eq6122
    | (have j0 := eq6122 X0
       grind)
    | exact resolve eq6122 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6122
  have eq6124 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6123 X0
       have i₂ := eq631 (M.op X0 X0)
       grind)
    | exact superpose eq631 eq6123
    | (have j0 := eq6123 X0
       grind)
    | exact resolve eq6123 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6123
  have eq7800 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq265 X0
       have i₂ := eq631 X0
       grind)
    | exact superpose eq631 eq265
    | (have j0 := eq265 X0
       grind)
    | exact resolve eq265 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq7801 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7800 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq7800
    | (have j0 := eq7800 X0
       grind)
    | exact resolve eq7800 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7800
  have eq7802 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7801 X0
       have i₂ := eq631 X0
       grind)
    | exact superpose eq631 eq7801
    | (have j0 := eq7801 X0
       grind)
    | exact resolve eq7801 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq7803 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7802 X0
       have i₂ := eq631 (M.op X0 X0)
       grind)
    | exact superpose eq631 eq7802
    | (have j0 := eq7802 X0
       grind)
    | exact resolve eq7802 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7802
  have eq7804 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq7803 X0
       have i₂ := eq631 X0
       grind)
    | exact superpose eq631 eq7803
    | (have j0 := eq7803 X0
       grind)
    | exact resolve eq7803 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7803
  have eq7805 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7804 X0
       have i₂ := eq631 (M.op X0 X0)
       grind)
    | exact superpose eq631 eq7804
    | (have j0 := eq7804 X0
       grind)
    | exact resolve eq7804 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7804
  have eq14558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq109 eq74
    | (have j0 := eq74 (σ y) (σ x)
       grind)
    | exact resolve eq74 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq109
  have eq14559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq14558
    | exact resolve eq14558 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14558
  have eq14570 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14559
       have r₂ := eq29
       grind)
    | exact resolve eq14559 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14559
  have eq14574 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14570 eq68
    | exact resolve eq68 eq14570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14570
  have eq14605 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq14574
    | exact resolve eq14574 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14574
  have eq14606 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq14605
  have eq14622 : (τ (σ x)) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14606 eq120
    | exact resolve eq120 eq14606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14606
  have eq14648 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq14622
    | exact resolve eq14622 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14622
  have eq14649 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq14648
  have eq14665 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56
       have i₂ := eq14649
       grind)
    | exact superpose eq14649 eq56
    | exact resolve eq56 eq14649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14675 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq14649
       grind)
    | exact superpose eq14649 eq14
    | (have j0 := eq14 X0 x
       grind)
    | exact resolve eq14 eq14649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14698 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14665
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq14665
    | exact resolve eq14665 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14665
  have eq14969 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  have eq14976 : (k (σ x) (σ y)) = (σ (M.op (τ (σ x)) (τ (σ y)))) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14698 eq7805
    | exact resolve eq7805 eq14698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7805 eq14698
  have eq14977 : (k (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq14976
    | exact resolve eq14976 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14976
  have eq14979 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq14969
    | exact resolve eq14969 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14969
  have eq14989 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq14977
    | exact resolve eq14977 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14977
  have eq14993 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14989
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14989
    | exact resolve eq14989 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14989
  have eq14995 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq14993
    | exact resolve eq14993 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14993
  have eq14997 : (τ (σ x)) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq120 eq14995
    | exact resolve eq14995 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14995
  have eq14998 : x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq14997
    | exact resolve eq14997 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14997
  have eq14999 : x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) := by grind
  clear eq14998
  have eq15000 : (τ (σ y)) = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq120 eq14999
    | exact resolve eq14999 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14999
  have eq15001 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq15000
    | exact resolve eq15000 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15000
  have eq18978 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq528 x X0
       have i₂ := eq14649
       grind)
    | exact superpose eq14649 eq528
    | (have j0 := eq528 x X0
       grind)
    | exact resolve eq528 eq14649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq14649
  have eq19014 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq18978 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq18978
    | (have j0 := eq18978 X0
       grind)
    | exact resolve eq18978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18978
  have eq19022 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq19014 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19014
    | (have j0 := eq19014 X0
       grind)
    | exact resolve eq19014 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19014
  have eq21475 : ∀ X0 : G, y ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) x) = (M.op x (τ X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14675 (τ X0)
       have i₂ := eq631 X0
       grind)
    | exact superpose eq631 eq14675
    | (have j0 := eq14675 (τ X0)
       grind)
    | exact resolve eq14675 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq14675
  have eq21489 : ∀ X0 : G, y ≠ (τ (M.op X0 X0)) ∨ (τ (k X0 (σ x))) = (M.op x (τ X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq21475 X0
       have i₂ := eq558 X0
       grind)
    | exact superpose eq558 eq21475
    | (have j0 := eq21475 X0
       grind)
    | exact resolve eq21475 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq21475
  have eq60346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14979 eq15001
    | exact resolve eq15001 eq14979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14979 eq15001
  have eq60361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq60346
  have eq60364 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq60361
       have r₂ := eq29
       grind)
    | exact resolve eq60361 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60361
  have eq84624 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq60364 eq120
    | exact resolve eq120 eq60364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60364
  have eq84689 : y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq84624
    | exact resolve eq84624 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84624
  have eq84690 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq84689
  have eq84707 : (τ (σ x)) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq84690 eq120
    | exact resolve eq120 eq84690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq84690
  have eq84771 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq84707
    | exact resolve eq84707 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84707
  have eq84772 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq84771
  have eq85611 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq84772
       grind)
    | exact superpose eq84772 eq100
    | exact resolve eq100 eq84772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84772
  have eq85674 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85611
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq85611
    | exact resolve eq85611 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85611
  have eq85710 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq85674 eq19022
    | (have j0 := eq19022 (σ y)
       grind)
    | (have r₁ := eq19022 (σ y)
       have r₂ := eq85674
       grind)
    | exact resolve eq19022 eq85674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19022
  have eq85716 : y ≠ (τ (σ y)) ∨ (τ (k (σ y) (σ x))) = (M.op x (τ (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq85674 eq21489
    | (have j0 := eq21489 (σ y)
       grind)
    | exact resolve eq21489 eq85674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21489 eq85674
  have eq85725 : y ≠ (τ (σ y)) ∨ (τ (k (σ y) (σ x))) = (M.op x (τ (σ y))) ∨ x = (M.op y y) := by grind
  clear eq85716
  have eq85732 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq85710
  have eq85733 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq85732
  have eq85745 : (τ (k (σ y) (σ x))) = (M.op x (τ (σ y))) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq85725
       have r₂ := eq31
       grind)
    | exact resolve eq85725 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85725
  have eq85748 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq85733
    | exact resolve eq85733 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85733
  have eq85763 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq85745
    | exact resolve eq85745 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85745
  have eq85767 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq107 eq85763
    | exact resolve eq85763 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq85763
  have eq85769 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85767
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq85767
    | exact resolve eq85767 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85767
  have eq86612 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq85769
       grind)
    | exact superpose eq85769 eq93
    | exact resolve eq93 eq85769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85769
  have eq86645 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq86612
    | exact resolve eq86612 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86612
  have eq86663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq86645 eq85748
    | exact resolve eq85748 eq86645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85748 eq86645
  have eq86665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq86663
  have eq86669 : x = (M.op y y) := by
    first
    | (have r₁ := eq86665
       have r₂ := eq29
       grind)
    | exact resolve eq86665 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86665
  have eq87385 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq86669
       grind)
    | exact superpose eq86669 eq100
    | exact resolve eq100 eq86669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq87399 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq86669
       grind)
    | exact superpose eq86669 eq14
    | (have j0 := eq14 y X0
       grind)
    | exact resolve eq14 eq86669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87404 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq529 y X0
       have i₂ := eq86669
       grind)
    | exact superpose eq86669 eq529
    | (have j0 := eq529 y X0
       grind)
    | exact resolve eq529 eq86669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq86669
  have eq87415 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq87404 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87404
    | (have j0 := eq87404 X0
       grind)
    | exact resolve eq87404 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87404
  have eq87431 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq87385
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87385
    | exact resolve eq87385 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87385
  have eq87436 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq87415 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq87415
    | (have j0 := eq87415 X0
       grind)
    | exact resolve eq87415 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq87415
  have eq87472 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  have eq87477 : (k (σ x) (σ y)) = (σ (M.op (τ (σ x)) (τ (σ y)))) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq87431 eq6124
    | exact resolve eq6124 eq87431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6124 eq87431
  have eq87496 : (k (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq31 eq87477
    | exact resolve eq87477 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq87477
  have eq87497 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28 eq87472
    | exact resolve eq87472 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87472
  have eq87508 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq30 eq87496
    | exact resolve eq87496 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87496
  have eq87512 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq87508
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq87508
    | exact resolve eq87508 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87508
  have eq87516 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq22 eq87512
    | exact resolve eq87512 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87512
  have eq87518 : (τ (σ x)) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq68 eq87516
    | exact resolve eq87516 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87516
  have eq87520 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq87518
    | exact resolve eq87518 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87518
  have eq88211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq87520 eq87497
    | exact resolve eq87497 eq87520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87497 eq87520
  have eq88213 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq88211
       have r₂ := eq29
       grind)
    | exact resolve eq88211 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88211
  have eq89003 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq88213 eq68
    | exact resolve eq68 eq88213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq88213
  have eq89178 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq89003
    | exact resolve eq89003 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq89003
  have eq89179 : x = (M.op x x) := by grind
  clear eq89178
  have eq89183 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq89179
       grind)
    | exact superpose eq89179 eq56
    | exact resolve eq56 eq89179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq89351 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq89183
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq89183
    | exact resolve eq89183 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq89183
  have eq93554 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq87399 x
       have i₂ := eq89179
       grind)
    | exact superpose eq89179 eq87399
    | (have j0 := eq87399 x
       grind)
    | (have r₁ := eq87399 x
       have r₂ := eq89179
       grind)
    | exact resolve eq87399 eq89179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87399 eq89179
  have eq93568 : (M.op x y) = (k y x) := by grind
  clear eq93554
  have eq93571 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq93568
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq93568
    | exact resolve eq93568 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq93568
  have eq93577 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq93571
       grind)
    | exact superpose eq93571 eq93
    | exact resolve eq93 eq93571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq93571
  have eq93606 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq22 eq93577
    | exact resolve eq93577 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq93577
  have eq97287 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq89351 eq87436
    | (have j0 := eq87436 (σ x)
       grind)
    | (have r₁ := eq87436 (σ x)
       have r₂ := eq89351
       grind)
    | exact resolve eq87436 eq89351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87436 eq89351
  have eq97300 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq97287
  have eq97303 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq93606 eq97300
    | exact resolve eq97300 eq93606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93606 eq97300
  have eq97306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq97303
    | exact resolve eq97303 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq97303
  have eq97308 : False := by grind
  exact eq97308

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pyx_pyy_pxx_pyx_pyx_pxx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq9 X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq73 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq75 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq76 X0
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq73
    | exact resolve eq73 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq78
       have i₂ := eq77 (τ sF4)
       grind)
    | exact superpose eq77 eq78
    | exact resolve eq78 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq80 : y = (k y y) ∨ (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq79
    | exact resolve eq79 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq80
    | exact resolve eq80 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82 : (M.op y y) = (k y (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq81
    | exact resolve eq81 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq81
  have eq83 : (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq82
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq82
    | exact resolve eq82 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq82
  have eq84 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq83
       have i₂ := eq77 (τ sF5)
       grind)
    | exact superpose eq77 eq83
    | exact resolve eq83 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq111 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq128 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq14
    | (have j0 := eq14 (τ (σ y)) x
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq147 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq140 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq140 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq140 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq149 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq130
       have i₂ := eq77 sF4
       grind)
    | exact superpose eq77 eq130
    | exact resolve eq130 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq151 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq77 (τ sF4)
       grind)
    | exact superpose eq77 eq128
    | exact resolve eq128 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq157 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq147
    | (have j0 := eq147 X0 X1
       grind)
    | (have r₁ := eq147 X0 X0
       have r₂ := eq77 X0
       grind)
    | exact resolve eq147 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq159 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq149
       have i₂ := eq77 sF5
       grind)
    | exact superpose eq77 eq149
    | exact resolve eq149 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq161 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq151
       have i₂ := eq77 (τ sF5)
       grind)
    | exact superpose eq77 eq151
    | exact resolve eq151 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq167 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq169 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq159
       have i₂ := eq77 sF5
       grind)
    | exact superpose eq77 eq159
    | exact resolve eq159 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq171 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq161
       have i₂ := eq77 (τ sF5)
       grind)
    | exact superpose eq77 eq161
    | exact resolve eq161 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq177 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq183 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq309 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq11
    | (have j0 := eq11 X0 X1
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq309
    | (have j0 := eq309 X0 X1
       grind)
    | (have r₁ := eq309 X0 X0
       have r₂ := eq77 X0
       grind)
    | exact resolve eq309 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq315 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ (k X0 X1) = (k X1 X1) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq313
    | (have j0 := eq313 X0 X1
       grind)
    | (have r₁ := eq313 X0 X0
       have r₂ := eq77 X0
       grind)
    | exact resolve eq313 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq399 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq77 sF4
       grind)
    | exact superpose eq77 eq75
    | exact resolve eq75 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq400 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq399
       have i₂ := eq77 sF5
       grind)
    | exact superpose eq77 eq399
    | exact resolve eq399 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq401 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq400
       have i₂ := eq77 sF5
       grind)
    | exact superpose eq77 eq400
    | exact resolve eq400 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq400
  have eq446 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq169 eq33
    | exact resolve eq33 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  have eq450 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq171 eq15
    | exact resolve eq15 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq450
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq450
    | exact resolve eq450 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq459 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq452 eq15
    | exact resolve eq15 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq463 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq459
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq459
    | exact resolve eq459 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq465 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq463
    | exact resolve eq463 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq476 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq465 eq15
    | exact resolve eq15 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq476
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq476
    | exact resolve eq476 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq478 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq477
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq477
    | exact resolve eq477 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq479 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq478
    | exact resolve eq478 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq480 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq479 eq84
    | (have r₁ := eq84
       have r₂ := eq479
       grind)
    | exact resolve eq84 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq479 eq15
    | exact resolve eq15 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq491 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq480
  have eq492 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq486
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq486
    | exact resolve eq486 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq495 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq492
    | exact resolve eq492 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq503 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq495 eq111
    | exact resolve eq111 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq546 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq503 eq311
    | (have j0 := eq311 (τ (σ y)) X0
       grind)
    | (have r₁ := eq311 (τ (σ y)) x
       have r₂ := eq503
       grind)
    | exact resolve eq311 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq548 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq171 eq311
    | (have j0 := eq311 (τ (σ y)) X0
       grind)
    | (have r₁ := eq311 (τ (σ y)) x
       have r₂ := eq171
       grind)
    | exact resolve eq311 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq552 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | (have j0 := eq548 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq553 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq546 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq574 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq169 eq401
    | (have r₁ := eq401
       have r₂ := eq169
       grind)
    | exact resolve eq401 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq574
  have eq576 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq575
       have r₂ := eq401
       grind)
    | exact resolve eq575 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq655 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq553 eq42
    | exact resolve eq42 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq667 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq655 eq15
    | exact resolve eq15 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq668 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq667
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq667
    | exact resolve eq667 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq669 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq668
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq668
    | exact resolve eq668 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq670 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq669
    | exact resolve eq669 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq671 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq670
  have eq672 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq671 eq36
    | exact resolve eq36 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq671
  have eq691 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq672
       have i₂ := eq111 sF5 sF5
       grind)
    | exact superpose eq111 eq672
    | exact resolve eq672 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq707 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq315
    | (have j0 := eq315 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq315 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq315
    | (have j0 := eq315 (σ y) (σ x)
       grind)
    | exact resolve eq315 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq722 : ∀ X0 : G, (M.op x y) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq691 eq311
    | (have j0 := eq311 (τ (σ y)) X0
       grind)
    | exact resolve eq311 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq831 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq169 eq709
    | (have r₁ := eq709
       have r₂ := eq169
       grind)
    | exact resolve eq709 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq831
  have eq833 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq832
  have eq835 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq833
       have r₂ := eq447
       grind)
    | exact resolve eq833 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq833
  have eq939 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq552 eq42
    | exact resolve eq42 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq940 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by grind
  clear eq939
  have eq978 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq940 eq707
    | (have r₁ := eq707
       have r₂ := eq940
       grind)
    | exact resolve eq707 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq940 eq15
    | exact resolve eq15 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq992 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq978
  have eq993 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq992
  have eq995 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq987
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq987
    | exact resolve eq987 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq998 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq26 eq995
    | exact resolve eq995 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1010 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq998 eq15
    | exact resolve eq15 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1011 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq1010
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1010
    | exact resolve eq1010 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1012 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq1011
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1011
    | exact resolve eq1011 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1013 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1012
    | exact resolve eq1012 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1014 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1013 eq84
    | (have r₁ := eq84
       have r₂ := eq1013
       grind)
    | exact resolve eq84 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1028 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq1014
  have eq1152 : (k (τ (σ y)) (τ (σ x))) = (τ (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq835 eq111
    | exact resolve eq111 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq1159 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1152
       have i₂ := eq111 sF4 sF4
       grind)
    | exact superpose eq111 eq1152
    | exact resolve eq1152 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1219 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1159 eq465
    | exact resolve eq465 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq1220 : (k (τ (σ x)) (τ (σ x))) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1159 eq183
    | (have j0 := eq183 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq183 (τ (σ y)) (τ (σ x))
       have r₂ := eq1159
       grind)
    | exact resolve eq183 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1159
  have eq1225 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1220
  have eq1226 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1219
  have eq1233 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq1225
    | exact resolve eq1225 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1234 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1226
       have r₂ := eq446
       grind)
    | exact resolve eq1226 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1275 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1234 eq15
    | exact resolve eq15 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1275
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1275
    | exact resolve eq1275 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1284 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1281
    | exact resolve eq1281 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1306 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq169 eq1284
    | exact resolve eq1284 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq1284
  have eq1313 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1306
  have eq1315 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1313
       have r₂ := eq576
       grind)
    | exact resolve eq1313 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq1313
  have eq1316 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1315
       have r₂ := eq401
       grind)
    | exact resolve eq1315 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1355 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1316 eq682
    | (have r₁ := eq682
       have r₂ := eq1316
       grind)
    | exact resolve eq682 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1375 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1355
  have eq1376 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1375
  have eq1420 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1376 eq401
    | exact resolve eq401 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1423 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1420
  have eq1425 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq1423
       have r₂ := eq682
       grind)
    | exact resolve eq1423 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq1423
  have eq2143 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq993 eq15
    | exact resolve eq15 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq2151 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2143
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq2143
    | exact resolve eq2143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2155 : (k (σ x) (σ x)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2151
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2151
    | exact resolve eq2151 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq2156 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2155
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2155
    | exact resolve eq2155 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq3272 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1233
  have eq3284 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3272
       have r₂ := eq1234
       grind)
    | exact resolve eq3272 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234 eq3272
  have eq3298 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2156 eq15
    | exact resolve eq15 eq2156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq3303 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3298
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq3298
    | exact resolve eq3298 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298
  have eq3304 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3303
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq3303
    | exact resolve eq3303 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303
  have eq3305 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3304
    | exact resolve eq3304 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304
  have eq3306 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3305 eq84
    | (have r₁ := eq84
       have r₂ := eq3305
       grind)
    | exact resolve eq84 eq3305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq3315 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3305 eq15
    | exact resolve eq15 eq3305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305
  have eq3320 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq3306
  have eq3321 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3315
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq3315
    | exact resolve eq3315 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq3324 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3321
    | exact resolve eq3321 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3349 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3324 eq1425
    | (have r₁ := eq1425
       have r₂ := eq3324
       grind)
    | exact resolve eq1425 eq3324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425 eq3324
  have eq3356 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq3349
  have eq3357 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq3356
  have eq3404 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq3357 eq111
    | exact resolve eq111 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3645 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq3404 eq311
    | (have j0 := eq311 (τ (σ y)) X0
       grind)
    | (have r₁ := eq311 (τ (σ y)) x
       have r₂ := eq3404
       grind)
    | exact resolve eq311 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404
  have eq3650 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have j0 := eq3645 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3645
  have eq3666 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3650 X0
       have j1 := eq722 X0
       grind)
    | (have r₁ := eq3650 X0
       have r₂ := eq722 X0
       grind)
    | exact resolve eq3650 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq3650
  have eq3789 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3666 eq42
    | exact resolve eq42 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq3809 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3789 eq15
    | exact resolve eq15 eq3789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789
  have eq3812 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3809
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq3809
    | exact resolve eq3809 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809
  have eq3814 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3812
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq3812
    | exact resolve eq3812 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq3815 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq3814
    | exact resolve eq3814 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq3816 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq3815
  have eq5142 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3284 eq15
    | exact resolve eq15 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq5148 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5142
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq5142
    | exact resolve eq5142 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142
  have eq5149 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq5148
  have eq7026 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ y)) (τ (σ x)))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq491 eq15
    | exact resolve eq15 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq7053 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7026
       have i₂ := eq15 (τ sF5) (τ sF4)
       grind)
    | exact superpose eq15 eq7026
    | exact resolve eq7026 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026
  have eq7060 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7053
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq7053
    | exact resolve eq7053 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7053
  have eq7063 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq7060
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq7060
    | exact resolve eq7060 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7060
  have eq11520 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq5149 eq15
    | exact resolve eq15 eq5149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq11552 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11520
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq11520
    | exact resolve eq11520 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11520
  have eq11554 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11552
    | exact resolve eq11552 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11552
  have eq11555 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq11554
       have r₂ := eq446
       grind)
    | exact resolve eq11554 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq11554
  have eq11611 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq11555 eq33
    | exact resolve eq33 eq11555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11613 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq11555 eq709
    | exact resolve eq709 eq11555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq11616 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq11555
  have eq11619 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq11613
  have eq11622 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq11619
       have r₂ := eq11616
       grind)
    | exact resolve eq11619 eq11616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11619
  have eq27340 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ y)) (τ (σ x)))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1028 eq15
    | exact resolve eq15 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq27376 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq27340
       have i₂ := eq15 (τ sF5) (τ sF4)
       grind)
    | exact superpose eq15 eq27340
    | exact resolve eq27340 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27340
  have eq27389 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq27376
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq27376
    | exact resolve eq27376 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27376
  have eq27390 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq27389
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq27389
    | exact resolve eq27389 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27389
  have eq28047 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq7063 eq15
    | exact resolve eq15 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7063
  have eq28081 : (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq28047
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq28047
    | exact resolve eq28047 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28047
  have eq28082 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq28081
  have eq28109 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq28082 eq11622
    | (have r₁ := eq11622
       have r₂ := eq28082
       grind)
    | exact resolve eq11622 eq28082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28121 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq28082
  have eq28126 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq28109
  have eq28149 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq28126
       have r₂ := eq11611
       grind)
    | exact resolve eq28126 eq11611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28126
  have eq28217 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1376 eq28149
    | exact resolve eq28149 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq28220 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq28149 eq33
    | exact resolve eq33 eq28149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28149
  have eq28230 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq28217
  have eq28237 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq28230
       have r₂ := eq28220
       grind)
    | exact resolve eq28230 eq28220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28220 eq28230
  have eq28241 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq28237
       have r₂ := eq28121
       grind)
    | exact resolve eq28237 eq28121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28121 eq28237
  have eq28358 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq28241 eq11616
    | (have r₁ := eq11616
       have r₂ := eq28241
       grind)
    | exact resolve eq11616 eq28241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11616 eq28241
  have eq28380 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq28358
  have eq28381 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq28380
  have eq28412 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq28381
       have r₂ := eq11611
       grind)
    | exact resolve eq28381 eq11611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28381
  have eq28458 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq28412 eq401
    | (have r₁ := eq401
       have r₂ := eq28412
       grind)
    | exact resolve eq401 eq28412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28412
  have eq28464 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq28458
  have eq28465 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq28464
  have eq28525 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq28465
  have eq124201 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq27390 eq311
    | (have j0 := eq311 (τ (σ y)) X0
       grind)
    | (have r₁ := eq311 (τ (σ y)) x
       have r₂ := eq27390
       grind)
    | exact resolve eq311 eq27390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27390
  have eq124221 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq124201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124201
  have eq139556 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ y)) (τ (σ x)))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3320 eq15
    | exact resolve eq15 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq139624 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq139556
       have i₂ := eq15 (τ sF5) (τ sF4)
       grind)
    | exact superpose eq15 eq139556
    | exact resolve eq139556 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139556
  have eq139648 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq139624
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq139624
    | exact resolve eq139624 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139624
  have eq139660 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq139648
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq139648
    | exact resolve eq139648 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139648
  have eq220322 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq124221 eq42
    | exact resolve eq42 eq124221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124221
  have eq220459 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq220322 eq15
    | exact resolve eq15 eq220322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220322
  have eq220512 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq220459
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq220459
    | exact resolve eq220459 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220459
  have eq220513 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq220512
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq220512
    | exact resolve eq220512 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220512
  have eq220514 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq220513
    | exact resolve eq220513 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220513
  have eq220515 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq220514
  have eq220548 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq220515 eq11622
    | (have r₁ := eq11622
       have r₂ := eq220515
       grind)
    | exact resolve eq11622 eq220515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11622 eq220515
  have eq220591 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq220548
  have eq220774 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq220591 eq33
    | exact resolve eq33 eq220591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220591
  have eq220790 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq220774
       have r₂ := eq3816
       grind)
    | exact resolve eq220774 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220774
  have eq220937 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq220790 eq28525
    | (have r₁ := eq28525
       have r₂ := eq220790
       grind)
    | exact resolve eq28525 eq220790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28525 eq220790
  have eq221016 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq220937
  have eq221017 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq221016
  have eq221238 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq221017 eq111
    | exact resolve eq111 eq221017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221017
  have eq223007 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq221238 eq311
    | (have j0 := eq311 (τ (σ y)) X0
       grind)
    | (have r₁ := eq311 (τ (σ y)) x
       have r₂ := eq221238
       grind)
    | exact resolve eq311 eq221238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221238
  have eq223029 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq223007 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223007
  have eq226907 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq223029 eq42
    | exact resolve eq42 eq223029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223029
  have eq227160 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq226907 eq15
    | exact resolve eq15 eq226907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226907
  have eq227215 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq227160
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq227160
    | exact resolve eq227160 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227160
  have eq227216 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq227215
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq227215
    | exact resolve eq227215 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227215
  have eq227217 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq227216
    | exact resolve eq227216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227216
  have eq227218 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq227217
  have eq227219 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq227218 eq36
    | exact resolve eq36 eq227218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227257 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq227218 eq3816
    | exact resolve eq3816 eq227218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq227735 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  have eq227954 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq227257
       have r₂ := eq227735
       grind)
    | exact resolve eq227257 eq227735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227257
  have eq227991 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq227219
       have i₂ := eq111 sF5 sF5
       grind)
    | exact superpose eq111 eq227219
    | exact resolve eq227219 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227219
  have eq228231 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq227954 eq227735
    | exact resolve eq227735 eq227954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227954
  have eq228265 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq228231
  have eq230825 : ∀ X0 : G, (M.op x y) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq227991 eq311
    | (have j0 := eq311 (τ (σ y)) X0
       grind)
    | exact resolve eq311 eq227991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227991
  have eq232351 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq139660 eq311
    | (have j0 := eq311 (τ (σ y)) X0
       grind)
    | (have r₁ := eq311 (τ (σ y)) x
       have r₂ := eq139660
       grind)
    | exact resolve eq311 eq139660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139660
  have eq232374 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq232351 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232351
  have eq232418 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq232374 X0
       grind)
    | (have r₁ := eq232374 X0
       have r₂ := eq227735
       grind)
    | exact resolve eq232374 eq227735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227735 eq232374
  have eq232465 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have j0 := eq232418 X0
       grind)
    | (have r₁ := eq232418 X0
       have r₂ := eq228265
       grind)
    | exact resolve eq232418 eq228265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228265 eq232418
  have eq232482 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq232465 X0
       have j1 := eq230825 X0
       grind)
    | (have r₁ := eq232465 X0
       have r₂ := eq230825 X0
       grind)
    | exact resolve eq232465 eq230825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230825 eq232465
  have eq233169 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq232482 eq42
    | exact resolve eq42 eq232482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq232482
  have eq233312 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq233169 eq15
    | exact resolve eq15 eq233169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233169
  have eq233371 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq233312
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq233312
    | exact resolve eq233312 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233312
  have eq233401 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq233371
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq233371
    | exact resolve eq233371 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233371
  have eq233403 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq233401
    | exact resolve eq233401 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233401
  have eq233404 : (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq233403
  have eq233408 : (M.op x y) = (τ (k (σ y) (σ x))) := by
    first
    | exact superpose eq233404 eq36
    | exact resolve eq36 eq233404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq233536 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq233404 eq11611
    | (have r₁ := eq11611
       have r₂ := eq233404
       grind)
    | exact resolve eq11611 eq233404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11611
  have eq233760 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq233536
  have eq233846 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq233408
       have i₂ := eq111 sF4 sF5
       grind)
    | exact superpose eq111 eq233408
    | exact resolve eq233408 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233408
  have eq234005 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq233846 eq15
    | exact resolve eq15 eq233846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234035 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) := by
    first
    | (have i₁ := eq234005
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq234005
    | exact resolve eq234005 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234005
  have eq234036 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq234035
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq234035
    | exact resolve eq234035 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234035
  have eq234221 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq233760 eq33
    | exact resolve eq33 eq233760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234222 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq233760 eq401
    | (have r₁ := eq401
       have r₂ := eq233760
       grind)
    | exact resolve eq401 eq233760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq233760
  have eq234231 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq234222
  have eq234232 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq234231
  have eq234241 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq233404 eq234221
    | exact resolve eq234221 eq233404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234221
  have eq234413 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq234232 eq111
    | exact resolve eq111 eq234232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234431 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq234232
  have eq234461 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq234413
       have i₂ := eq111 sF4 sF5
       grind)
    | exact superpose eq111 eq234413
    | exact resolve eq234413 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq234413
  have eq234469 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq233846 eq234461
    | exact resolve eq234461 eq233846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234461
  have eq234895 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq234469 eq707
    | (have r₁ := eq707
       have r₂ := eq234469
       grind)
    | exact resolve eq707 eq234469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq234469
  have eq235032 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq234895
  have eq235054 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq233846 eq235032
    | exact resolve eq235032 eq233846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233846 eq235032
  have eq235055 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq235054
  have eq237057 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq235055 eq15
    | exact resolve eq15 eq235055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235055
  have eq237145 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq237057
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq237057
    | exact resolve eq237057 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237057
  have eq237147 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq237145
    | exact resolve eq237145 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237145
  have eq237148 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq233404 eq237147
    | exact resolve eq237147 eq233404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237147
  have eq237149 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq237148
       have r₂ := eq234241
       grind)
    | exact resolve eq237148 eq234241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234241 eq237148
  have eq237378 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq237149 eq311
    | (have j0 := eq311 (σ y) X0
       grind)
    | (have r₁ := eq311 (σ y) x
       have r₂ := eq237149
       grind)
    | exact resolve eq311 eq237149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237149
  have eq237395 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have j0 := eq237378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237378
  have eq237406 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq237395 eq32
    | (have j1 := eq237395 (σ x)
       grind)
    | exact resolve eq32 eq237395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237395
  have eq237593 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq237406 eq33
    | exact resolve eq33 eq237406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237406
  have eq237611 : (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq237593
       have r₂ := eq233404
       grind)
    | exact resolve eq237593 eq233404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233404 eq237593
  have eq238053 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq237611 eq35
    | exact resolve eq35 eq237611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq237611
  have eq238305 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq238053 eq234036
    | exact resolve eq234036 eq238053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234036
  have eq238306 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq238053 eq26
    | exact resolve eq26 eq238053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq238053
  have eq238977 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq238306 eq227218
    | exact resolve eq227218 eq238306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227218
  have eq238993 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq238977
       have r₂ := eq234431
       grind)
    | exact resolve eq238977 eq234431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234431 eq238977
  have eq239759 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq238993 eq311
    | (have j0 := eq311 (σ y) X0
       grind)
    | (have r₁ := eq311 (σ y) x
       have r₂ := eq238993
       grind)
    | exact resolve eq311 eq238993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq238993
  have eq239775 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq239759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239759
  have eq240188 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq239775 eq32
    | (have j1 := eq239775 (σ x)
       grind)
    | exact resolve eq32 eq239775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq239775
  have eq240191 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq238305 eq240188
    | exact resolve eq240188 eq238305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238305 eq240188
  have eq240247 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq240191 eq33
    | exact resolve eq33 eq240191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq240191
  have eq240273 : False := by grind
  exact eq240273

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pyy_y_pxy_x_pyx_pyx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq16
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq73
    | exact resolve eq73 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq382 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq298
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1104 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (k x y) := by
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
  have eq1105 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1107 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq28 X0 X0
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq14
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1119 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1120 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1121 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1119 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1119 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq1119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1122 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1120 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq1120 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq1120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1126 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1116 (τ X0)
       have i₂ := eq382 X0 X0
       grind)
    | exact superpose eq382 eq1116
    | (have j0 := eq1116 (τ X0)
       grind)
    | exact resolve eq1116 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1121 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1121
    | (have j0 := eq1121 (σ X0) X1
       grind)
    | exact resolve eq1121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1129 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1122
    | (have j0 := eq1122 (σ X0) X1
       grind)
    | exact resolve eq1122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 (τ X0) X1
       have i₂ := eq382 X0 X0
       grind)
    | exact superpose eq382 eq1122
    | (have j0 := eq1122 (τ X0) X1
       grind)
    | exact resolve eq1122 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq1122
  have eq6607 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq41
    | exact resolve eq41 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq6608 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6607
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6607
    | exact resolve eq6607 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq6612 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq6608
    | exact resolve eq6608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608
  have eq6889 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1114
    | (have j0 := eq1114 (σ X1) (σ X1)
       grind)
    | exact resolve eq1114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq19377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6612 eq1107
    | exact resolve eq1107 eq6612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq6612
  have eq19390 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq19377
       have r₂ := eq27
       grind)
    | exact resolve eq19377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19377
  have eq19781 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq19390 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) x
       have r₂ := eq19390
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq19390
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq19390
       grind)
    | exact resolve eq14 eq19390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19782 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19781
  have eq19794 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19782 eq19390
    | exact resolve eq19390 eq19782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19390 eq19782
  have eq19795 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq19794
  have eq19818 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19795 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq19795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19795
  have eq19833 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq19818
  have eq19840 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32 eq19833
    | exact resolve eq19833 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19833
  have eq19841 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq19840
  have eq19854 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq19841 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq19841
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq19841
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq19841
       grind)
    | exact resolve eq14 eq19841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19855 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19854
  have eq20023 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19855 eq19841
    | exact resolve eq19841 eq19855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19841 eq19855
  have eq20024 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq20023
  have eq20037 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20024 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq20024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024
  have eq20052 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq20037
  have eq20059 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq20052
    | exact resolve eq20052 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20052
  have eq20060 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20059
  have eq20074 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq20060
       grind)
    | exact superpose eq20060 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq20060
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq20060
       grind)
    | exact resolve eq14 eq20060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20075 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20074
  have eq20141 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20075 x
       grind)
    | exact superpose eq20075 eq18
    | (have j1 := eq20075 x
       grind)
    | exact resolve eq18 eq20075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20142 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20060
       have i₂ := eq20075 y
       grind)
    | exact superpose eq20075 eq20060
    | exact resolve eq20060 eq20075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20060 eq20075
  have eq20143 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20142
  have eq20151 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq20141
       grind)
    | exact superpose eq20141 eq40
    | exact resolve eq40 eq20141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20141
  have eq20156 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20151
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20151
    | exact resolve eq20151 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20151
  have eq20162 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq20156
    | exact resolve eq20156 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20156
  have eq20178 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1127 y X0
       have i₂ := eq20143
       grind)
    | exact superpose eq20143 eq1127
    | (have j0 := eq1127 y X0
       grind)
    | exact resolve eq1127 eq20143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20143
  have eq20191 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20178
  have eq20199 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20191 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20191
    | (have j0 := eq20191 X0
       grind)
    | exact resolve eq20191 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20191
  have eq20303 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20199 eq26
    | (have j1 := eq20199 (σ x)
       grind)
    | exact resolve eq26 eq20199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20199
  have eq20310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20162 eq20303
    | exact resolve eq20303 eq20162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20162 eq20303
  have eq20312 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20310
       have r₂ := eq27
       grind)
    | exact resolve eq20310 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20310
  have eq20319 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq20312
       grind)
    | exact superpose eq20312 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq20312
       grind)
    | exact resolve eq28 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20320 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq20312
       grind)
    | exact superpose eq20312 eq14
    | (have j0 := eq14 x X0
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq20312
       grind)
    | exact resolve eq14 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20321 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20320
  have eq20322 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20319
  have eq20334 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20312
       have i₂ := eq20321 x
       grind)
    | exact superpose eq20321 eq20312
    | exact resolve eq20312 eq20321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20321
  have eq20335 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20334
  have eq20349 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1129 x X0
       have i₂ := eq20335
       grind)
    | exact superpose eq20335 eq1129
    | (have j0 := eq1129 x X0
       grind)
    | exact resolve eq1129 eq20335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20351 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6889 x x
       have i₂ := eq20335
       grind)
    | exact superpose eq20335 eq6889
    | (have j0 := eq6889 x x
       grind)
    | exact resolve eq6889 eq20335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20335
  have eq20355 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20351
  have eq20356 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20355
  have eq20358 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20349
  have eq20366 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20356
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20356
    | exact resolve eq20356 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20356
  have eq20367 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20358 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20358
    | (have j0 := eq20358 X0
       grind)
    | exact resolve eq20358 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20358
  have eq20667 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20322 y
       grind)
    | exact superpose eq20322 eq18
    | (have j1 := eq20322 y
       grind)
    | exact resolve eq18 eq20322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20322
  have eq20679 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq20667
       grind)
    | exact superpose eq20667 eq40
    | exact resolve eq40 eq20667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20667
  have eq20683 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20679
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20679
    | exact resolve eq20679 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20679
  have eq20689 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq20683
    | exact resolve eq20683 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20683
  have eq20715 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20367 eq26
    | (have j1 := eq20367 (σ y)
       grind)
    | exact resolve eq26 eq20367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20367
  have eq20729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20689 eq20715
    | exact resolve eq20715 eq20689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20689 eq20715
  have eq20731 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20729
       have r₂ := eq27
       grind)
    | exact resolve eq20729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20729
  have eq20733 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20731 eq1105
    | (have r₁ := eq1105
       have r₂ := eq20731
       grind)
    | exact resolve eq1105 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq20734 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20731 eq27
    | exact resolve eq27 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20735 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20733
  have eq20943 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20735 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) x
       have r₂ := eq20735
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq20735
       grind)
    | exact resolve eq14 eq20735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20944 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20943 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20943
  have eq21012 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20944 eq20735
    | exact resolve eq20735 eq20944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20735 eq20944
  have eq21017 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21012
  have eq21032 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21017 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq21017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21017
  have eq21047 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21032
  have eq21054 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq21047
    | exact resolve eq21047 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21047
  have eq21102 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21054 eq153
    | exact resolve eq153 eq21054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq21054
  have eq21113 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq21102
    | exact resolve eq21102 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21102
  have eq21430 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21113 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq21113
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq21113
       grind)
    | exact resolve eq14 eq21113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21431 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21430
  have eq21607 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21431 eq21113
    | exact resolve eq21113 eq21431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21113 eq21431
  have eq21616 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq21607
  have eq21698 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21616 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq21616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21616
  have eq21713 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq21698
  have eq21720 : x = (M.op x x) ∨ x = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq21713
    | exact resolve eq21713 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21713
  have eq21726 : y = (M.op y y) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21720
       have r₂ := eq1104
       grind)
    | exact resolve eq21720 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq21720
  have eq21741 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (k x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq21726
       grind)
    | exact superpose eq21726 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq21726
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq21726
       grind)
    | exact resolve eq14 eq21726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21742 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (k x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21741 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21741
  have eq21763 : (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21742 x
       grind)
    | exact superpose eq21742 eq18
    | (have j1 := eq21742 x
       grind)
    | exact resolve eq18 eq21742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21764 : y = (k y y) ∨ x = (k x y) ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21726
       have i₂ := eq21742 y
       grind)
    | exact superpose eq21742 eq21726
    | exact resolve eq21726 eq21742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21726 eq21742
  have eq21768 : y = (k y y) ∨ x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq21764
  have eq21777 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq21763
       grind)
    | exact superpose eq21763 eq40
    | exact resolve eq40 eq21763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21763
  have eq21782 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21777
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21777
    | exact resolve eq21777 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21777
  have eq21788 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq21782
    | exact resolve eq21782 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21782
  have eq21804 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1127 y X0
       have i₂ := eq21768
       grind)
    | exact superpose eq21768 eq1127
    | (have j0 := eq1127 y X0
       grind)
    | exact resolve eq1127 eq21768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21768
  have eq21817 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21804
  have eq21825 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq21817 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21817
    | (have j0 := eq21817 X0
       grind)
    | exact resolve eq21817 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21817
  have eq21959 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21825 eq26
    | (have j1 := eq21825 (σ x)
       grind)
    | exact resolve eq26 eq21825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21825
  have eq21970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21788 eq21959
    | exact resolve eq21959 eq21788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21788 eq21959
  have eq21972 : x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21970
       have r₂ := eq27
       grind)
    | exact resolve eq21970 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21970
  have eq21976 : x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq21972
       grind)
    | exact superpose eq21972 eq1106
    | exact resolve eq1106 eq21972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq21981 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6889 x y
       have i₂ := eq21972
       grind)
    | exact superpose eq21972 eq6889
    | (have j0 := eq6889 y y
       grind)
    | exact resolve eq6889 eq21972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6889 eq21972
  have eq21985 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq21981
  have eq21986 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq21976
  have eq21989 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21985
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21985
    | exact resolve eq21985 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21985
  have eq21995 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21989
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21989
    | exact resolve eq21989 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21989
  have eq21997 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21995
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21995
    | exact resolve eq21995 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21995
  have eq21998 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq21997
    | exact resolve eq21997 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21997
  have eq21999 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21998
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21998
    | exact resolve eq21998 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21998
  have eq22000 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20366 eq21999
    | exact resolve eq21999 eq20366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20366 eq21999
  have eq22046 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq21986
       grind)
    | exact superpose eq21986 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq21986
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq21986
       grind)
    | exact resolve eq14 eq21986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22047 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22046 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22046
  have eq22077 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22047 x
       grind)
    | exact superpose eq22047 eq18
    | (have j1 := eq22047 x
       grind)
    | exact resolve eq18 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22078 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21986
       have i₂ := eq22047 y
       grind)
    | exact superpose eq22047 eq21986
    | exact resolve eq21986 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21986 eq22047
  have eq22085 : y = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq22078
  have eq22096 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq22077
       grind)
    | exact superpose eq22077 eq40
    | exact resolve eq40 eq22077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22077
  have eq22101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22096
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22096
    | exact resolve eq22096 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22096
  have eq22107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq22101
    | exact resolve eq22101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22101
  have eq22368 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1127 y X0
       have i₂ := eq22085
       grind)
    | exact superpose eq22085 eq1127
    | (have j0 := eq1127 y X0
       grind)
    | exact resolve eq1127 eq22085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22085
  have eq22381 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22368
  have eq22389 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22381 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22381
    | (have j0 := eq22381 X0
       grind)
    | exact resolve eq22381 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22381
  have eq22550 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22389 eq26
    | (have j1 := eq22389 (σ x)
       grind)
    | exact resolve eq26 eq22389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22389
  have eq22566 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20312 eq22550
    | exact resolve eq22550 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20312 eq22550
  have eq22585 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22566 eq22107
    | exact resolve eq22107 eq22566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22107 eq22566
  have eq22590 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq22585
  have eq22607 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22590
       have r₂ := eq20734
       grind)
    | exact resolve eq22590 eq20734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22590
  have eq22625 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq22607
       grind)
    | exact superpose eq22607 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq22607
       grind)
    | exact resolve eq28 eq22607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22626 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq22607
       grind)
    | exact superpose eq22607 eq14
    | (have j0 := eq14 x X0
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq22607
       grind)
    | exact resolve eq14 eq22607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22627 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22626
  have eq22628 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22625 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22625
  have eq22645 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22607
       have i₂ := eq22627 x
       grind)
    | exact superpose eq22627 eq22607
    | exact resolve eq22607 eq22627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22607 eq22627
  have eq22648 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq22645
  have eq22663 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1129 x X0
       have i₂ := eq22648
       grind)
    | exact superpose eq22648 eq1129
    | (have j0 := eq1129 x X0
       grind)
    | exact resolve eq1129 eq22648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22648
  have eq22672 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22663
  have eq22681 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22672 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22672
    | (have j0 := eq22672 X0
       grind)
    | exact resolve eq22672 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22672
  have eq22752 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22628 y
       grind)
    | exact superpose eq22628 eq18
    | (have j1 := eq22628 y
       grind)
    | exact resolve eq18 eq22628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22628
  have eq22767 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq22752
       grind)
    | exact superpose eq22752 eq40
    | exact resolve eq40 eq22752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq22752
  have eq22771 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22767
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22767
    | exact resolve eq22767 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22767
  have eq22777 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22771
    | exact resolve eq22771 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22771
  have eq22819 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22681 eq26
    | (have j1 := eq22681 (σ y)
       grind)
    | exact resolve eq26 eq22681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22681
  have eq22851 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20731 eq22819
    | exact resolve eq22819 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20731 eq22819
  have eq22872 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22851 eq22777
    | exact resolve eq22777 eq22851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22777 eq22851
  have eq22877 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22872
  have eq22894 : x = (M.op x y) := by
    first
    | (have r₁ := eq22877
       have r₂ := eq20734
       grind)
    | exact resolve eq22877 eq20734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20734 eq22877
  have eq22905 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22894
       grind)
    | exact superpose eq22894 eq18
    | exact resolve eq18 eq22894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22906 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq22894
       grind)
    | exact superpose eq22894 eq22
    | exact resolve eq22 eq22894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq22944 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22906 eq20
    | exact resolve eq20 eq22906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22906
  have eq45127 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22000 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) x
       have r₂ := eq22000
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq22000
       grind)
    | (have r₁ := eq14 (M.op x y) x
       have r₂ := eq22000
       grind)
    | exact resolve eq14 eq22000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45128 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq45127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45127
  have eq174157 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45128 eq22000
    | exact resolve eq22000 eq45128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22000 eq45128
  have eq174166 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq174157
  have eq174256 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq174166 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq174166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174166
  have eq174271 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq174256
  have eq174278 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32 eq174271
    | exact resolve eq174271 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq174271
  have eq174332 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq174278 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq174278
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq174278
       grind)
    | (have r₁ := eq14 (M.op x y) x
       have r₂ := eq174278
       grind)
    | exact resolve eq14 eq174278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174333 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq174332 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174332
  have eq174622 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq174333 eq174278
    | exact resolve eq174278 eq174333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174278 eq174333
  have eq174627 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq174622
  have eq174668 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq174627 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq174627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq174672 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq174627 eq1130
    | (have j0 := eq1130 (σ x) X0
       grind)
    | exact resolve eq1130 eq174627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq174627
  have eq174679 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq174672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174672
  have eq174683 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq174668
  have eq174688 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq174679
    | exact resolve eq174679 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174679
  have eq174690 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq174683
    | exact resolve eq174683 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq174683
  have eq174713 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq174688 X0
       have i₂ := eq22894
       grind)
    | exact superpose eq22894 eq174688
    | exact resolve eq174688 eq22894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174688
  have eq174715 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq174690
       have i₂ := eq22894
       grind)
    | exact superpose eq22894 eq174690
    | exact resolve eq174690 eq22894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22894 eq174690
  have eq174716 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq174715
  have eq174739 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq174713 X0
       have j1 := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq174713 X0
       have r₂ := eq28 X0 y
       grind)
    | (have r₁ := eq174713 X0
       have r₂ := eq28 X0 (M.op x y)
       grind)
    | exact resolve eq174713 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq174713
  have eq174758 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq174739 eq22905
    | exact resolve eq22905 eq174739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174759 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq174739 eq174716
    | exact resolve eq174716 eq174739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174716 eq174739
  have eq174764 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq174759
  have eq174796 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq174764 eq1129
    | (have j0 := eq1129 (M.op x y) X0
       grind)
    | exact resolve eq1129 eq174764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq174764
  have eq174805 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq174796 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174796
  have eq174814 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20 eq174805
    | (have j0 := eq174805 X0
       grind)
    | exact resolve eq174805 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174805
  have eq174841 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22944 eq174814
    | exact resolve eq174814 eq22944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174814
  have eq174960 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq174758 eq37
    | exact resolve eq37 eq174758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174758
  have eq174971 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq174960
    | exact resolve eq174960 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174960
  have eq174993 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22944 eq174971
    | exact resolve eq174971 eq22944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174971
  have eq175280 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq174841 eq26
    | (have j1 := eq174841 (σ y)
       grind)
    | exact resolve eq26 eq174841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174841
  have eq175317 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq174993 eq175280
    | exact resolve eq175280 eq174993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174993 eq175280
  have eq175318 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq175317
  have eq175347 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq175318
       grind)
    | exact superpose eq175318 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq175318
       grind)
    | exact resolve eq14 eq175318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175348 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq175347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175347
  have eq175377 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq175318
       have i₂ := eq175348 y
       grind)
    | exact superpose eq175348 eq175318
    | exact resolve eq175318 eq175348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175318
  have eq175383 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22905
       have i₂ := eq175348 sF0
       grind)
    | exact superpose eq175348 eq22905
    | exact resolve eq22905 eq175348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22905 eq175348
  have eq175386 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq175377
  have eq175406 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1127 y X0
       have i₂ := eq175386
       grind)
    | exact superpose eq175386 eq1127
    | (have j0 := eq1127 y X0
       grind)
    | exact resolve eq1127 eq175386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq175386
  have eq175419 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq175406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175406
  have eq175427 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq175419 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq175419
    | (have j0 := eq175419 X0
       grind)
    | exact resolve eq175419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq175419
  have eq176594 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq175383 eq37
    | exact resolve eq37 eq175383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq175383
  have eq176604 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq176594
    | exact resolve eq176594 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq176594
  have eq176626 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22944 eq176604
    | exact resolve eq176604 eq22944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176604
  have eq176927 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq175427 eq26
    | (have j1 := eq175427 (σ x)
       grind)
    | exact resolve eq26 eq175427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq175427
  have eq176943 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176626 eq176927
    | exact resolve eq176927 eq176626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176626 eq176927
  have eq176944 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq176943
  have eq176948 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq176944 eq27
    | exact resolve eq27 eq176944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq176944
  have eq176950 : False := by grind
  exact eq176950

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pyy_y_pxy_y_pyx_pyx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq53 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq67 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq78 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (k x y) := by
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
  have eq85 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq67
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq98
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq95
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq123 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq154 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq156
  have eq182 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq200 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq523 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq3001 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq154 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq154
    | (have j0 := eq154 x
       grind)
    | exact resolve eq154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq3007 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3001
  have eq3011 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3007
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3007
    | exact resolve eq3007 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3028 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq3011
       have r₂ := eq14 (σ x) x
       grind)
    | exact resolve eq3011 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3035 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3028 eq49
    | exact resolve eq49 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3161 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq182
    | (have j0 := eq182 y
       grind)
    | exact resolve eq182 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq3166 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3161
  have eq3169 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3166
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq3166
    | exact resolve eq3166 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166
  have eq3193 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq3169
       have r₂ := eq14 (σ y) x
       grind)
    | exact resolve eq3169 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3217 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3193 eq78
    | exact resolve eq78 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3343 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq200
    | (have j0 := eq200 (M.op x y)
       grind)
    | exact resolve eq200 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq3347 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3343
  have eq3349 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq125 eq3347
    | exact resolve eq3347 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq3347
  have eq3380 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3349
       have r₂ := eq14 (σ (M.op x y)) x
       grind)
    | exact resolve eq3349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3420 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3380 eq159
    | exact resolve eq159 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq4570 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ x) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ x) (σ (τ X0))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq523 x (τ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq523
    | (have j0 := eq523 (τ X0) (τ X0)
       grind)
    | exact resolve eq523 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq523
  have eq4665 : ∀ X0 : G, (k (σ x) X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ x) (σ (τ X0))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4570 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4570
    | (have j0 := eq4570 X0
       grind)
    | exact resolve eq4570 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4570
  have eq4752 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ x) (σ (τ X0))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4665 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4665
    | (have j0 := eq4665 X0
       grind)
    | exact resolve eq4665 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4665
  have eq4839 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) ≠ X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4752 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4752
    | (have j0 := eq4752 X0
       grind)
    | exact resolve eq4752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4752
  have eq4922 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) ≠ X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4839 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4839
    | (have j0 := eq4839 X0
       grind)
    | exact resolve eq4839 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4839
  have eq5004 : ∀ X0 : G, (k (σ x) X0) ≠ X0 ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4922 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4922
    | (have j0 := eq4922 X0
       grind)
    | exact resolve eq4922 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4922
  have eq8261 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3193 eq109
    | exact resolve eq109 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq8262 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3028 eq110
    | exact resolve eq110 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq8785 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3380 eq164
    | exact resolve eq164 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3380
  have eq11134 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq8261
       grind)
    | exact superpose eq8261 eq16
    | exact resolve eq16 eq8261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8261
  have eq11183 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3217 eq11134
    | exact resolve eq11134 eq3217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11134
  have eq11186 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq11183
       have r₂ := eq14 y x
       grind)
    | exact resolve eq11183 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11183
  have eq11187 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11186
       grind)
    | exact superpose eq11186 eq67
    | exact resolve eq67 eq11186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq11212 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq3193 eq11187
    | exact resolve eq11187 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193 eq11187
  have eq11219 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq8262
       grind)
    | exact superpose eq8262 eq16
    | exact resolve eq16 eq8262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262
  have eq11270 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3035 eq11219
    | exact resolve eq11219 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11219
  have eq11273 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq11270
       have r₂ := eq14 x x
       grind)
    | exact resolve eq11270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11270
  have eq11274 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11273
       grind)
    | exact superpose eq11273 eq43
    | exact resolve eq43 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq11299 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq3028 eq11274
    | exact resolve eq11274 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028 eq11274
  have eq11860 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8785 eq16
    | exact resolve eq16 eq8785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8785
  have eq11915 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3420 eq11860
    | exact resolve eq11860 eq3420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11860
  have eq11918 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq14 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq11915
       have r₂ := eq14 (M.op x y) x
       grind)
    | exact resolve eq11915 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11915
  have eq18430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq18431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq18430
    | exact resolve eq18430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18430
  have eq18442 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq18431
       have r₂ := eq27
       grind)
    | exact resolve eq18431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18431
  have eq18446 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq18442
    | exact resolve eq18442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18442
  have eq18448 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18446 eq3217
    | exact resolve eq3217 eq18446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq18469 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18448
       have i₂ := eq11186
       grind)
    | exact superpose eq11186 eq18448
    | exact resolve eq18448 eq11186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18448
  have eq18478 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq18469
    | exact resolve eq18469 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18469
  have eq18479 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq18478
  have eq18481 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18479 eq3035
    | exact resolve eq3035 eq18479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18479
  have eq18502 : (τ (σ x)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18481
       have i₂ := eq11273
       grind)
    | exact superpose eq11273 eq18481
    | exact resolve eq18481 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18481
  have eq18511 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq18502
    | exact resolve eq18502 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18502
  have eq18512 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq18511
  have eq18520 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11212
       have i₂ := eq18512
       grind)
    | exact superpose eq18512 eq11212
    | exact resolve eq11212 eq18512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18524 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq18512
       grind)
    | exact superpose eq18512 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq18512
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq18512
       grind)
    | exact resolve eq14 eq18512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18512
  have eq18525 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18524 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18524
  have eq18529 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18520
    | exact resolve eq18520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18520
  have eq18825 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18529 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) x
       have r₂ := eq18529
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq18529
       grind)
    | exact resolve eq14 eq18529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18529
  have eq18826 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18825 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18825
  have eq18893 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq18525 x
       grind)
    | exact superpose eq18525 eq66
    | exact resolve eq66 eq18525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18525
  have eq18933 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18893
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18893
    | exact resolve eq18893 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18893
  have eq18958 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq18933
    | exact resolve eq18933 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18933
  have eq19481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18826 eq18958
    | exact resolve eq18958 eq18826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18826 eq18958
  have eq19486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq19481
  have eq19488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19486
    | exact resolve eq19486 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19486
  have eq19513 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19488
       have r₂ := eq27
       grind)
    | exact resolve eq19488 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19488
  have eq19800 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11299
       have i₂ := eq19513
       grind)
    | exact superpose eq19513 eq11299
    | exact resolve eq11299 eq19513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19803 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 X0 x
       have i₂ := eq19513
       grind)
    | exact superpose eq19513 eq59
    | (have j0 := eq59 X0 x
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq19513
       grind)
    | exact resolve eq59 eq19513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19513
  have eq19806 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19803 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19803
  have eq19809 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19800
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19800
    | exact resolve eq19800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19800
  have eq19827 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19809 eq59
    | (have j0 := eq59 X0 (σ x)
       grind)
    | (have r₁ := eq59 X0 (σ x)
       have r₂ := eq19809
       grind)
    | exact resolve eq59 eq19809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19809
  have eq19830 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19827
  have eq20266 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq19806 y
       grind)
    | exact superpose eq19806 eq66
    | exact resolve eq66 eq19806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19806
  have eq20344 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20266
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20266
    | exact resolve eq20266 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20266
  have eq20367 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20344
    | exact resolve eq20344 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20344
  have eq20841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19830 eq20367
    | exact resolve eq20367 eq19830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19830 eq20367
  have eq20875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20841
  have eq20890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq20875
    | exact resolve eq20875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20875
  have eq20904 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20890
       have r₂ := eq27
       grind)
    | exact resolve eq20890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20890
  have eq21188 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20904 eq85
    | (have r₁ := eq85
       have r₂ := eq20904
       grind)
    | exact resolve eq85 eq20904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq20904
  have eq21190 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21188
  have eq36508 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21190 eq53
    | exact resolve eq53 eq21190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq21190
  have eq36534 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq36508
    | exact resolve eq36508 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36508
  have eq36541 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36534 eq3217
    | exact resolve eq3217 eq36534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3217 eq36534
  have eq36562 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36541
       have i₂ := eq11186
       grind)
    | exact superpose eq11186 eq36541
    | exact resolve eq36541 eq11186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11186 eq36541
  have eq36571 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq36562
    | exact resolve eq36562 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36562
  have eq36860 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36571 eq3035
    | exact resolve eq3035 eq36571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36571
  have eq36881 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36860
       have i₂ := eq11273
       grind)
    | exact superpose eq11273 eq36860
    | exact resolve eq36860 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36860
  have eq36890 : x = (M.op x x) ∨ y = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq36881
    | exact resolve eq36881 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36881
  have eq36892 : y = (k x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq36890
       have r₂ := eq84
       grind)
    | exact resolve eq36890 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq36890
  have eq36896 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq36892
       grind)
    | exact superpose eq36892 eq44
    | exact resolve eq44 eq36892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq36908 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq36892
       grind)
    | exact superpose eq36892 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq36892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36892
  have eq36909 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq36908
  have eq36914 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36909
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36909
    | exact resolve eq36909 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36909
  have eq36924 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36896
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36896
    | exact resolve eq36896 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36896
  have eq36938 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11212
       have i₂ := eq36914
       grind)
    | exact superpose eq36914 eq11212
    | exact resolve eq11212 eq36914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36942 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq36914
       grind)
    | exact superpose eq36914 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq36914
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq36914
       grind)
    | exact resolve eq14 eq36914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36914
  have eq36943 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq36942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36942
  have eq36947 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36938
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36938
    | exact resolve eq36938 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36938
  have eq37253 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq36947 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) x
       have r₂ := eq36947
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq36947
       grind)
    | exact resolve eq14 eq36947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36947
  have eq37254 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq37253 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37253
  have eq37694 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq36943 x
       grind)
    | exact superpose eq36943 eq66
    | exact resolve eq66 eq36943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36943
  have eq37740 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37694
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37694
    | exact resolve eq37694 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37694
  have eq37792 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq37740
    | exact resolve eq37740 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37740
  have eq38466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37254 eq37792
    | exact resolve eq37792 eq37254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37254 eq37792
  have eq38471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq38466
  have eq38479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq38471
    | exact resolve eq38471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38471
  have eq38506 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq38479
       have r₂ := eq27
       grind)
    | exact resolve eq38479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38479
  have eq38514 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11299
       have i₂ := eq38506
       grind)
    | exact superpose eq38506 eq11299
    | exact resolve eq11299 eq38506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38517 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 X0 x
       have i₂ := eq38506
       grind)
    | exact superpose eq38506 eq59
    | (have j0 := eq59 X0 x
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq38506
       grind)
    | exact resolve eq59 eq38506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38506
  have eq38520 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq38517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38517
  have eq38523 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38514
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38514
    | exact resolve eq38514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38514
  have eq38832 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38523 eq59
    | (have j0 := eq59 X0 (σ x)
       grind)
    | (have r₁ := eq59 X0 (σ x)
       have r₂ := eq38523
       grind)
    | exact resolve eq59 eq38523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38523
  have eq38835 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq38832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38832
  have eq39386 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq38520 y
       grind)
    | exact superpose eq38520 eq66
    | exact resolve eq66 eq38520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38520
  have eq39534 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39386
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39386
    | exact resolve eq39386 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39386
  have eq39557 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq39534
    | exact resolve eq39534 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39534
  have eq40097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38835 eq39557
    | exact resolve eq39557 eq38835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38835 eq39557
  have eq40162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq40097
  have eq40181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq40162
    | exact resolve eq40162 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40162
  have eq40195 : y = (M.op x y) := by
    first
    | (have r₁ := eq40181
       have r₂ := eq27
       grind)
    | exact resolve eq40181 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40181
  have eq40197 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq40195 eq20
    | exact resolve eq20 eq40195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40415 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40197
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40197
    | exact resolve eq40197 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40197
  have eq40458 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq40415 eq26
    | exact resolve eq26 eq40415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119717 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq36924 eq5004
    | (have j0 := eq5004 (σ y)
       grind)
    | (have r₁ := eq5004 (σ y)
       have r₂ := eq36924
       grind)
    | exact resolve eq5004 eq36924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004 eq36924
  have eq119722 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq119717
  have eq119729 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq119722
    | exact resolve eq119722 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq119722
  have eq119731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40415 eq119729
    | exact resolve eq119729 eq40415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119729
  have eq119733 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq119731
       have r₂ := eq27
       grind)
    | exact resolve eq119731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119731
  have eq119734 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40415 eq119733
    | exact resolve eq119733 eq40415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119733
  have eq120027 : (τ (σ x)) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq119734 eq3035
    | exact resolve eq3035 eq119734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035 eq119734
  have eq120048 : (τ (σ x)) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120027
       have i₂ := eq11273
       grind)
    | exact superpose eq11273 eq120027
    | exact resolve eq120027 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11273 eq120027
  have eq120057 : x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq120048
    | exact resolve eq120048 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq120048
  have eq120058 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq120057
  have eq120063 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq120058 eq3420
    | exact resolve eq3420 eq120058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420 eq120058
  have eq120104 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq11918 eq120063
    | exact resolve eq120063 eq11918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11918 eq120063
  have eq120117 : (τ (σ (M.op x y))) = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq40195 eq120104
    | exact resolve eq120104 eq40195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120104
  have eq120126 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq120117
    | exact resolve eq120117 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq120117
  have eq120135 : y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq40195 eq120126
    | exact resolve eq120126 eq40195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120126
  have eq120136 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq120135
  have eq120147 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11212
       have i₂ := eq120136
       grind)
    | exact superpose eq120136 eq11212
    | exact resolve eq11212 eq120136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11212
  have eq120155 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq120136
       grind)
    | exact superpose eq120136 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq120136
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq120136
       grind)
    | exact resolve eq14 eq120136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120136
  have eq120156 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq120155 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120155
  have eq120164 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40415 eq120147
    | exact resolve eq120147 eq40415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120147
  have eq120177 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120164
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120164
    | exact resolve eq120164 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq120164
  have eq120186 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40415 eq120177
    | exact resolve eq120177 eq40415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120177
  have eq120218 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq120186 eq14
    | (have j0 := eq14 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq14 (σ (M.op x y)) x
       have r₂ := eq120186
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq120186
       grind)
    | exact resolve eq14 eq120186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120186
  have eq120219 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq120218 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120218
  have eq120434 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq120156 x
       grind)
    | exact superpose eq120156 eq66
    | exact resolve eq66 eq120156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq120156
  have eq120501 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40415 eq120434
    | exact resolve eq120434 eq40415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40415 eq120434
  have eq120640 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120501
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120501
    | exact resolve eq120501 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120501
  have eq120740 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq120640
    | exact resolve eq120640 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120640
  have eq121661 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq120219 eq120740
    | exact resolve eq120740 eq120219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120219 eq120740
  have eq121671 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq121661
  have eq121684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40458 eq121671
    | exact resolve eq121671 eq40458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121671
  have eq121791 : x = (M.op x x) := by
    first
    | (have r₁ := eq121684
       have r₂ := eq27
       grind)
    | exact resolve eq121684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121684
  have eq121885 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11299
       have i₂ := eq121791
       grind)
    | exact superpose eq121791 eq11299
    | exact resolve eq11299 eq121791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11299
  have eq121892 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq59 X0 x
       have i₂ := eq121791
       grind)
    | exact superpose eq121791 eq59
    | (have j0 := eq59 X0 x
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq121791
       grind)
    | exact resolve eq59 eq121791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121791
  have eq121895 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq121892 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121892
  have eq121902 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq121885
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121885
    | exact resolve eq121885 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq121885
  have eq121924 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq121902 eq59
    | (have j0 := eq59 X0 (σ x)
       grind)
    | (have r₁ := eq59 X0 (σ x)
       have r₂ := eq121902
       grind)
    | exact resolve eq59 eq121902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq121902
  have eq121927 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq121924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121924
  have eq122482 : (σ (M.op x (M.op x y))) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq121895 sF0
       grind)
    | exact superpose eq121895 eq123
    | exact resolve eq123 eq121895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq121895
  have eq122708 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq40195 eq122482
    | exact resolve eq122482 eq40195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40195 eq122482
  have eq122833 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq122708
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122708
    | exact resolve eq122708 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq122708
  have eq122914 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq122833
    | exact resolve eq122833 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq122833
  have eq123615 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq121927 eq122914
    | exact resolve eq122914 eq121927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121927 eq122914
  have eq123858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40458 eq123615
    | exact resolve eq123615 eq40458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40458 eq123615
  have eq123984 : False := by grind
  exact eq123984

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pyy_y_pyx_x_pxy_pxy_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq67 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq66
       grind)
    | exact superpose eq66 eq16
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ y = (k y x) := by
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
  have eq85 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq91 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq95 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq66
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq67
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq98
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq95
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq156
  have eq3001 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq90 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq90
    | (have j0 := eq90 x
       grind)
    | exact resolve eq90 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq3007 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3001
  have eq3011 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3007
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3007
    | exact resolve eq3007 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3028 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq3011
       have r₂ := eq14 (σ x) x
       grind)
    | exact resolve eq3011 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3034 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3028 eq49
    | exact resolve eq49 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3156 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq91 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91
    | (have j0 := eq91 y
       grind)
    | exact resolve eq91 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq3161 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3156
  have eq3164 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3161
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq3161
    | exact resolve eq3161 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161
  have eq3188 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq3164
       have r₂ := eq14 (σ y) x
       grind)
    | exact resolve eq3164 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3164
  have eq3210 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3188 eq78
    | exact resolve eq78 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3339 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq126
    | (have j0 := eq126 (M.op x y)
       grind)
    | exact resolve eq126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq3343 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3339
  have eq3345 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq125 eq3343
    | exact resolve eq3343 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq3343
  have eq3376 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3345
       have r₂ := eq14 (σ (M.op x y)) x
       grind)
    | exact resolve eq3345 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3415 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3376 eq159
    | exact resolve eq159 eq3376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq8259 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3188 eq109
    | exact resolve eq109 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq8260 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3028 eq110
    | exact resolve eq110 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq8783 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3376 eq164
    | exact resolve eq164 eq3376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3376
  have eq11132 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq8259
       grind)
    | exact superpose eq8259 eq16
    | exact resolve eq16 eq8259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8259
  have eq11181 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3210 eq11132
    | exact resolve eq11132 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11132
  have eq11184 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq11181
       have r₂ := eq14 y x
       grind)
    | exact resolve eq11181 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq11185 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11184
       grind)
    | exact superpose eq11184 eq67
    | exact resolve eq67 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq11210 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq3188 eq11185
    | exact resolve eq11185 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3188 eq11185
  have eq11217 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq8260
       grind)
    | exact superpose eq8260 eq16
    | exact resolve eq16 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8260
  have eq11268 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3034 eq11217
    | exact resolve eq11217 eq3034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11217
  have eq11271 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq11268
       have r₂ := eq14 x x
       grind)
    | exact resolve eq11268 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11268
  have eq11272 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11271
       grind)
    | exact superpose eq11271 eq43
    | exact resolve eq43 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq11297 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq3028 eq11272
    | exact resolve eq11272 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028 eq11272
  have eq11858 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8783 eq16
    | exact resolve eq16 eq8783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8783
  have eq11913 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3415 eq11858
    | exact resolve eq11858 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11858
  have eq11916 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq14 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq11913
       have r₂ := eq14 (M.op x y) x
       grind)
    | exact resolve eq11913 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11913
  have eq18428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq18429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq18428
    | exact resolve eq18428 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18428
  have eq18440 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq18429
       have r₂ := eq27
       grind)
    | exact resolve eq18429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18429
  have eq18444 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq18440
    | exact resolve eq18440 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18440
  have eq18446 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq18444 eq3210
    | exact resolve eq3210 eq18444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18444
  have eq18467 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18446
       have i₂ := eq11184
       grind)
    | exact superpose eq11184 eq18446
    | exact resolve eq18446 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq18476 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq18467
    | exact resolve eq18467 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18467
  have eq18477 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq18476
  have eq18479 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18477 eq3034
    | exact resolve eq3034 eq18477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477
  have eq18500 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18479
       have i₂ := eq11271
       grind)
    | exact superpose eq11271 eq18479
    | exact resolve eq18479 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18479
  have eq18509 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq18500
    | exact resolve eq18500 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18500
  have eq18510 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18509
  have eq18518 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11210
       have i₂ := eq18510
       grind)
    | exact superpose eq18510 eq11210
    | exact resolve eq11210 eq18510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18521 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 X0 y
       have i₂ := eq18510
       grind)
    | exact superpose eq18510 eq59
    | (have j0 := eq59 X0 y
       grind)
    | (have r₁ := eq59 X0 y
       have r₂ := eq18510
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq18510
       grind)
    | exact resolve eq59 eq18510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18510
  have eq18524 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18521
  have eq18527 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18518
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18518
    | exact resolve eq18518 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18518
  have eq18822 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18527 eq59
    | (have j0 := eq59 X0 (σ y)
       grind)
    | (have r₁ := eq59 X0 (σ y)
       have r₂ := eq18527
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq18527
       grind)
    | exact resolve eq59 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18527
  have eq18825 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18822
  have eq18971 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq18524 x
       grind)
    | exact superpose eq18524 eq44
    | exact resolve eq44 eq18524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18524
  have eq19054 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18971
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18971
    | exact resolve eq18971 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18971
  have eq19069 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq19054
    | exact resolve eq19054 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19054
  have eq19812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18825 eq19069
    | exact resolve eq19069 eq18825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18825 eq19069
  have eq19847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19812
  have eq19862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19847
    | exact resolve eq19847 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19847
  have eq19876 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19862
       have r₂ := eq27
       grind)
    | exact resolve eq19862 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19862
  have eq19884 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11297
       have i₂ := eq19876
       grind)
    | exact superpose eq19876 eq11297
    | exact resolve eq11297 eq19876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19888 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq19876
       grind)
    | exact superpose eq19876 eq14
    | (have j0 := eq14 x X0
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq19876
       grind)
    | exact resolve eq14 eq19876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19876
  have eq19889 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19888
  have eq19893 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19884
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19884
    | exact resolve eq19884 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19884
  have eq20191 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19893 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq19893
       grind)
    | exact resolve eq14 eq19893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19893
  have eq20192 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20191 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20191
  have eq20272 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq19889 y
       grind)
    | exact superpose eq19889 eq44
    | exact resolve eq44 eq19889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19889
  have eq20301 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20272
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20272
    | exact resolve eq20272 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20272
  have eq20333 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20301
    | exact resolve eq20301 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20301
  have eq20877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20192 eq20333
    | exact resolve eq20333 eq20192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20192 eq20333
  have eq20878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20877
  have eq20882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq20878
    | exact resolve eq20878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20878
  have eq20907 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20882
       have r₂ := eq27
       grind)
    | exact resolve eq20882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20882
  have eq21191 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20907 eq85
    | (have r₁ := eq85
       have r₂ := eq20907
       grind)
    | exact resolve eq85 eq20907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq20907
  have eq21193 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq21191
  have eq34220 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21193 eq73
    | exact resolve eq73 eq21193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq21193
  have eq34246 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq34220
    | exact resolve eq34220 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34220
  have eq34253 : (τ (σ y)) = (k y y) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34246 eq3210
    | exact resolve eq3210 eq34246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3210 eq34246
  have eq34274 : (τ (σ y)) = (M.op y y) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34253
       have i₂ := eq11184
       grind)
    | exact superpose eq11184 eq34253
    | exact resolve eq34253 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11184 eq34253
  have eq34283 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq34274
    | exact resolve eq34274 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34274
  have eq34285 : (τ (σ x)) = (k x x) ∨ y = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34283 eq3034
    | exact resolve eq3034 eq34283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34283
  have eq34306 : (τ (σ x)) = (M.op x x) ∨ y = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34285
       have i₂ := eq11271
       grind)
    | exact superpose eq11271 eq34285
    | exact resolve eq34285 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34285
  have eq34315 : x = (M.op x x) ∨ y = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq34306
    | exact resolve eq34306 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34306
  have eq34317 : y = (k y x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq34315
       have r₂ := eq84
       grind)
    | exact resolve eq34315 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq34315
  have eq34607 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq34317
       grind)
    | exact superpose eq34317 eq66
    | exact resolve eq66 eq34317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq34619 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq34317
       grind)
    | exact superpose eq34317 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq34317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34317
  have eq34620 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq34619
  have eq34625 : y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34620
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34620
    | exact resolve eq34620 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34620
  have eq34635 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34607
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34607
    | exact resolve eq34607 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34607
  have eq34649 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11210
       have i₂ := eq34625
       grind)
    | exact superpose eq34625 eq11210
    | exact resolve eq11210 eq34625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34652 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 X0 y
       have i₂ := eq34625
       grind)
    | exact superpose eq34625 eq59
    | (have j0 := eq59 X0 y
       grind)
    | (have r₁ := eq59 X0 y
       have r₂ := eq34625
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq34625
       grind)
    | exact resolve eq59 eq34625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34625
  have eq34655 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34652
  have eq34658 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34649
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34649
    | exact resolve eq34649 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34649
  have eq34961 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34658 eq59
    | (have j0 := eq59 X0 (σ y)
       grind)
    | (have r₁ := eq59 X0 (σ y)
       have r₂ := eq34658
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq34658
       grind)
    | exact resolve eq59 eq34658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34658
  have eq34964 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34961 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34961
  have eq35514 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq34655 x
       grind)
    | exact superpose eq34655 eq44
    | exact resolve eq44 eq34655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34655
  have eq35673 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35514
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35514
    | exact resolve eq35514 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35514
  have eq35688 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq35673
    | exact resolve eq35673 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35673
  have eq36210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34964 eq35688
    | exact resolve eq35688 eq34964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34964 eq35688
  have eq36278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq36210
  have eq36297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq36278
    | exact resolve eq36278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36278
  have eq36311 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq36297
       have r₂ := eq27
       grind)
    | exact resolve eq36297 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36297
  have eq36319 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11297
       have i₂ := eq36311
       grind)
    | exact superpose eq36311 eq11297
    | exact resolve eq11297 eq36311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36323 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq36311
       grind)
    | exact superpose eq36311 eq14
    | (have j0 := eq14 x X0
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq36311
       grind)
    | exact resolve eq14 eq36311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36311
  have eq36324 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36323
  have eq36328 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36319
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36319
    | exact resolve eq36319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36319
  have eq36635 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36328 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq36328
       grind)
    | exact resolve eq14 eq36328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36328
  have eq36636 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36635
  have eq36756 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq36324 y
       grind)
    | exact superpose eq36324 eq44
    | exact resolve eq44 eq36324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36324
  have eq36791 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36756
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36756
    | exact resolve eq36756 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36756
  have eq36844 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq36791
    | exact resolve eq36791 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36791
  have eq37817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36636 eq36844
    | exact resolve eq36844 eq36636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36636 eq36844
  have eq37818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37817
  have eq37826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq37818
    | exact resolve eq37818 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37818
  have eq37851 : y = (M.op x y) := by
    first
    | (have r₁ := eq37826
       have r₂ := eq27
       grind)
    | exact resolve eq37826 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37826
  have eq37853 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq37851 eq20
    | exact resolve eq20 eq37851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38063 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq37853
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37853
    | exact resolve eq37853 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37853
  have eq38106 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq38063 eq26
    | exact resolve eq26 eq38063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq38183 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq38063 eq34635
    | exact resolve eq34635 eq38063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34635
  have eq43441 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq38183 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq38183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38183
  have eq43442 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq43441
  have eq43445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq38106 eq43442
    | exact resolve eq43442 eq38106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43442
  have eq43456 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq43445
       have r₂ := eq27
       grind)
    | exact resolve eq43445 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43445
  have eq124085 : (τ (σ x)) = (k x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq43456 eq3034
    | exact resolve eq3034 eq43456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034 eq43456
  have eq124106 : (τ (σ x)) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq124085
       have i₂ := eq11271
       grind)
    | exact superpose eq11271 eq124085
    | exact resolve eq124085 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11271 eq124085
  have eq124115 : x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq28 eq124106
    | exact resolve eq124106 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq124106
  have eq124116 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq124115
  have eq125215 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq124116 eq3415
    | exact resolve eq3415 eq124116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415 eq124116
  have eq125256 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq11916 eq125215
    | exact resolve eq125215 eq11916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11916 eq125215
  have eq125269 : (τ (σ (M.op x y))) = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq37851 eq125256
    | exact resolve eq125256 eq37851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125256
  have eq125278 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq125269
    | exact resolve eq125269 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq125269
  have eq125287 : y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq37851 eq125278
    | exact resolve eq125278 eq37851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125278
  have eq125288 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq125287
  have eq125299 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11210
       have i₂ := eq125288
       grind)
    | exact superpose eq125288 eq11210
    | exact resolve eq11210 eq125288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11210
  have eq125306 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq59 X0 y
       have i₂ := eq125288
       grind)
    | exact superpose eq125288 eq59
    | (have j0 := eq59 X0 y
       grind)
    | (have r₁ := eq59 X0 y
       have r₂ := eq125288
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq125288
       grind)
    | exact resolve eq59 eq125288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125288
  have eq125309 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq125306 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125306
  have eq125316 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38063 eq125299
    | exact resolve eq125299 eq38063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125299
  have eq125329 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq125316
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq125316
    | exact resolve eq125316 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq125316
  have eq125338 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38063 eq125329
    | exact resolve eq125329 eq38063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125329
  have eq125368 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq125338 eq59
    | (have j0 := eq59 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq59 X0 (σ (M.op x y))
       have r₂ := eq125338
       grind)
    | (have r₁ := eq59 X0 x
       have r₂ := eq125338
       grind)
    | exact resolve eq59 eq125338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq125338
  have eq125371 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq125368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125368
  have eq125974 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq125309 x
       grind)
    | exact superpose eq125309 eq44
    | exact resolve eq44 eq125309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq125309
  have eq126252 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38063 eq125974
    | exact resolve eq125974 eq38063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38063 eq125974
  have eq126394 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq126252
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126252
    | exact resolve eq126252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126252
  have eq126461 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq126394
    | exact resolve eq126394 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126394
  have eq128171 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq125371 eq126461
    | exact resolve eq126461 eq125371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125371 eq126461
  have eq128309 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq128171
  have eq128395 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38106 eq128309
    | exact resolve eq128309 eq38106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128309
  have eq128477 : x = (M.op x x) := by
    first
    | (have r₁ := eq128395
       have r₂ := eq27
       grind)
    | exact resolve eq128395 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128395
  have eq128526 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11297
       have i₂ := eq128477
       grind)
    | exact superpose eq128477 eq11297
    | exact resolve eq11297 eq128477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11297
  have eq128534 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq128477
       grind)
    | exact superpose eq128477 eq14
    | (have j0 := eq14 x X0
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq128477
       grind)
    | exact resolve eq14 eq128477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128477
  have eq128535 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq128534 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128534
  have eq128543 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq128526
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq128526
    | exact resolve eq128526 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq128526
  have eq128566 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq128543 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq128543
       grind)
    | exact resolve eq14 eq128543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128543
  have eq128567 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq128566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128566
  have eq128780 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq45
       have i₂ := eq128535 sF0
       grind)
    | exact superpose eq128535 eq45
    | exact resolve eq45 eq128535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq128535
  have eq128797 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq37851 eq128780
    | exact resolve eq128780 eq37851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37851 eq128780
  have eq128936 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq128797
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq128797
    | exact resolve eq128797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq128797
  have eq129016 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq128936
    | exact resolve eq128936 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq128936
  have eq131433 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq128567 eq129016
    | exact resolve eq129016 eq128567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128567 eq129016
  have eq131459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38106 eq131433
    | exact resolve eq131433 eq38106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38106 eq131433
  have eq131601 : False := by grind
  exact eq131601

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pyy_y_pyx_y_pxy_pxy_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq382 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq298
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1104 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (k y x) := by
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
  have eq1105 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq1107 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq28 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X0
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq14
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1119 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1120 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1121 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1119 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1119 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq1119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1122 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1120 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq1120 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq1120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1126 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1116 (τ X0)
       have i₂ := eq382 X0 X0
       grind)
    | exact superpose eq382 eq1116
    | (have j0 := eq1116 (τ X0)
       grind)
    | exact resolve eq1116 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1121 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1121
    | (have j0 := eq1121 (σ X0) X1
       grind)
    | exact resolve eq1121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1121 (τ X0) X1
       have i₂ := eq382 X0 X0
       grind)
    | exact superpose eq382 eq1121
    | (have j0 := eq1121 (τ X0) X1
       grind)
    | exact resolve eq1121 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1129 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1122
    | (have j0 := eq1122 (σ X0) X1
       grind)
    | exact resolve eq1122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 (τ X0) X1
       have i₂ := eq382 X0 X0
       grind)
    | exact superpose eq382 eq1122
    | (have j0 := eq1122 (τ X0) X1
       grind)
    | exact resolve eq1122 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq1122
  have eq6607 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq40
    | exact resolve eq40 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq6608 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6607
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6607
    | exact resolve eq6607 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq6612 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq6608
    | exact resolve eq6608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608
  have eq6889 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1114
    | (have j0 := eq1114 (σ X1) (σ X1)
       grind)
    | exact resolve eq1114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq19377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6612 eq1107
    | exact resolve eq1107 eq6612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq6612
  have eq19390 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq19377
       have r₂ := eq27
       grind)
    | exact resolve eq19377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19377
  have eq19755 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19390 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) x
       have r₂ := eq19390
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq19390
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq19390
       grind)
    | exact resolve eq14 eq19390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19756 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19755 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19755
  have eq19762 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19756 eq19390
    | exact resolve eq19390 eq19756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19390 eq19756
  have eq19767 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq19762
  have eq19778 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19767 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq19767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19767
  have eq19793 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq19778
  have eq19800 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq19793
    | exact resolve eq19793 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19793
  have eq19801 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19800
  have eq19814 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19801 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq19801
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq19801
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq19801
       grind)
    | exact resolve eq14 eq19801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19815 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19814
  have eq19843 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19815 eq19801
    | exact resolve eq19801 eq19815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19801 eq19815
  have eq19848 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19843
  have eq20011 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19848 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq19848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19848
  have eq20026 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20011
  have eq20033 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq20026
    | exact resolve eq20026 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20026
  have eq20034 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20033
  have eq20050 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq20034
       grind)
    | exact superpose eq20034 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq20034
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq20034
       grind)
    | exact resolve eq28 eq20034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20051 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq20034
       grind)
    | exact superpose eq20034 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq20034
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq20034
       grind)
    | exact resolve eq14 eq20034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20052 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20051 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20051
  have eq20053 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20050
  have eq20112 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20034
       have i₂ := eq20052 y
       grind)
    | exact superpose eq20052 eq20034
    | exact resolve eq20034 eq20052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20034 eq20052
  have eq20117 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20112
  have eq20131 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1129 y X0
       have i₂ := eq20117
       grind)
    | exact superpose eq20117 eq1129
    | (have j0 := eq1129 y X0
       grind)
    | exact resolve eq1129 eq20117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20117
  have eq20140 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20131
  have eq20149 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20140 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20140
    | (have j0 := eq20140 X0
       grind)
    | exact resolve eq20140 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20140
  have eq20211 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20053 x
       grind)
    | exact superpose eq20053 eq18
    | (have j1 := eq20053 x
       grind)
    | exact resolve eq18 eq20053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20053
  have eq20219 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq20211
       grind)
    | exact superpose eq20211 eq41
    | exact resolve eq41 eq20211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20211
  have eq20224 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20219
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20219
    | exact resolve eq20219 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20219
  have eq20230 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq20224
    | exact resolve eq20224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20224
  have eq20259 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20149 eq26
    | (have j1 := eq20149 (σ x)
       grind)
    | exact resolve eq26 eq20149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20149
  have eq20266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20230 eq20259
    | exact resolve eq20259 eq20230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20230 eq20259
  have eq20268 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20266
       have r₂ := eq27
       grind)
    | exact resolve eq20266 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20266
  have eq20276 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq20268
       grind)
    | exact superpose eq20268 eq14
    | (have j0 := eq14 x X0
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq20268
       grind)
    | exact resolve eq14 eq20268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20277 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20276
  have eq20287 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20277 y
       grind)
    | exact superpose eq20277 eq18
    | (have j1 := eq20277 y
       grind)
    | exact resolve eq18 eq20277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20288 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20268
       have i₂ := eq20277 x
       grind)
    | exact superpose eq20277 eq20268
    | exact resolve eq20268 eq20277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20277
  have eq20293 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20288
  have eq20299 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq20287
       grind)
    | exact superpose eq20287 eq41
    | exact resolve eq41 eq20287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20287
  have eq20303 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20299
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20299
    | exact resolve eq20299 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20299
  have eq20309 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq20303
    | exact resolve eq20303 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20303
  have eq20325 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1127 x X0
       have i₂ := eq20293
       grind)
    | exact superpose eq20293 eq1127
    | (have j0 := eq1127 x X0
       grind)
    | exact resolve eq1127 eq20293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20293
  have eq20338 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20325
  have eq20346 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20338 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20338
    | (have j0 := eq20338 X0
       grind)
    | exact resolve eq20338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20338
  have eq20691 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20346 eq26
    | (have j1 := eq20346 (σ y)
       grind)
    | exact resolve eq26 eq20346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20346
  have eq20705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20309 eq20691
    | exact resolve eq20691 eq20309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20309 eq20691
  have eq20707 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20705
       have r₂ := eq27
       grind)
    | exact resolve eq20705 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20705
  have eq20709 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20707 eq1105
    | (have r₁ := eq1105
       have r₂ := eq20707
       grind)
    | exact resolve eq1105 eq20707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq20710 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20707 eq27
    | exact resolve eq27 eq20707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20711 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20709
  have eq20913 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20711 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) x
       have r₂ := eq20711
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq20711
       grind)
    | exact resolve eq14 eq20711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20914 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20913 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20913
  have eq20975 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20914 eq20711
    | exact resolve eq20711 eq20914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20711 eq20914
  have eq20984 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20975
  have eq20997 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20984 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq20984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20984
  have eq21012 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20997
  have eq21019 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq21012
    | exact resolve eq21012 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21012
  have eq21032 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21019 eq108
    | exact resolve eq108 eq21019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq21019
  have eq21045 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq21032
    | exact resolve eq21032 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21032
  have eq21335 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21045 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq21045
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq21045
       grind)
    | exact resolve eq14 eq21045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21336 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21335
  have eq21567 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21336 eq21045
    | exact resolve eq21045 eq21336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21045 eq21336
  have eq21580 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq21567
  have eq21664 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21580 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq21580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21580
  have eq21679 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq21664
  have eq21686 : x = (M.op x x) ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq21679
    | exact resolve eq21679 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21679
  have eq21692 : y = (M.op y y) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21686
       have r₂ := eq1104
       grind)
    | exact resolve eq21686 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq21686
  have eq21706 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq21692
       grind)
    | exact superpose eq21692 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq21692
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq21692
       grind)
    | exact resolve eq28 eq21692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21707 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq21692
       grind)
    | exact superpose eq21692 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq21692
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq21692
       grind)
    | exact resolve eq14 eq21692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21708 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21707
  have eq21709 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21706
  have eq21723 : y = (k y y) ∨ x = (k y x) ∨ x = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21692
       have i₂ := eq21708 y
       grind)
    | exact superpose eq21708 eq21692
    | exact resolve eq21692 eq21708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21692 eq21708
  have eq21731 : y = (k y y) ∨ x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq21723
  have eq21746 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1129 y X0
       have i₂ := eq21731
       grind)
    | exact superpose eq21731 eq1129
    | (have j0 := eq1129 y X0
       grind)
    | exact resolve eq1129 eq21731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21731
  have eq21755 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21746 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21746
  have eq21764 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq21755 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21755
    | (have j0 := eq21755 X0
       grind)
    | exact resolve eq21755 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21755
  have eq21840 : (M.op x y) = (k x y) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21709 x
       grind)
    | exact superpose eq21709 eq18
    | (have j1 := eq21709 x
       grind)
    | exact resolve eq18 eq21709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21709
  have eq21852 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq21840
       grind)
    | exact superpose eq21840 eq41
    | exact resolve eq41 eq21840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21840
  have eq21857 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21852
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21852
    | exact resolve eq21852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21852
  have eq21863 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq21857
    | exact resolve eq21857 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21857
  have eq21900 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21764 eq26
    | (have j1 := eq21764 (σ x)
       grind)
    | exact resolve eq26 eq21764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21764
  have eq21911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21863 eq21900
    | exact resolve eq21900 eq21863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21863 eq21900
  have eq21913 : x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21911
       have r₂ := eq27
       grind)
    | exact resolve eq21911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21911
  have eq21917 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq21913
       grind)
    | exact superpose eq21913 eq1106
    | exact resolve eq1106 eq21913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq21922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6889 y x
       have i₂ := eq21913
       grind)
    | exact superpose eq21913 eq6889
    | (have j0 := eq6889 x x
       grind)
    | exact resolve eq6889 eq21913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6889 eq21913
  have eq21926 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq21922
  have eq21927 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq21917
  have eq21930 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21926
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21926
    | exact resolve eq21926 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21926
  have eq21936 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21930
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21930
    | exact resolve eq21930 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21930
  have eq21938 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21936
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21936
    | exact resolve eq21936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21936
  have eq21939 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq21938
    | exact resolve eq21938 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21938
  have eq21940 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21939
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21939
    | exact resolve eq21939 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21939
  have eq21941 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20707 eq21940
    | exact resolve eq21940 eq20707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21940
  have eq21986 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq21927
       grind)
    | exact superpose eq21927 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq21927
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq21927
       grind)
    | exact resolve eq28 eq21927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21987 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq21927
       grind)
    | exact superpose eq21927 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq21927
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq21927
       grind)
    | exact resolve eq14 eq21927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21988 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21987 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21987
  have eq21989 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21986 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21986
  have eq22012 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21927
       have i₂ := eq21988 y
       grind)
    | exact superpose eq21988 eq21927
    | exact resolve eq21927 eq21988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21927 eq21988
  have eq22023 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq22012
  have eq22040 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1129 y X0
       have i₂ := eq22023
       grind)
    | exact superpose eq22023 eq1129
    | (have j0 := eq1129 y X0
       grind)
    | exact resolve eq1129 eq22023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22023
  have eq22049 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22040
  have eq22058 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22049 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22049
    | (have j0 := eq22049 X0
       grind)
    | exact resolve eq22049 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22049
  have eq22388 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21989 x
       grind)
    | exact superpose eq21989 eq18
    | (have j1 := eq21989 x
       grind)
    | exact resolve eq18 eq21989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21989
  have eq22405 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq22388
       grind)
    | exact superpose eq22388 eq41
    | exact resolve eq41 eq22388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22388
  have eq22410 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22405
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22405
    | exact resolve eq22405 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22405
  have eq22416 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22410
    | exact resolve eq22410 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22410
  have eq22453 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22058 eq26
    | (have j1 := eq22058 (σ x)
       grind)
    | exact resolve eq26 eq22058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22058
  have eq22469 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20268 eq22453
    | exact resolve eq22453 eq20268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268 eq22453
  have eq22488 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22469 eq22416
    | exact resolve eq22416 eq22469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22416 eq22469
  have eq22493 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq22488
  have eq22510 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22493
       have r₂ := eq20710
       grind)
    | exact resolve eq22493 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22493
  have eq22528 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq22510
       grind)
    | exact superpose eq22510 eq14
    | (have j0 := eq14 x X0
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq22510
       grind)
    | exact resolve eq14 eq22510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22529 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22528 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22528
  have eq22544 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22529 y
       grind)
    | exact superpose eq22529 eq18
    | (have j1 := eq22529 y
       grind)
    | exact resolve eq18 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22545 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22510
       have i₂ := eq22529 x
       grind)
    | exact superpose eq22529 eq22510
    | exact resolve eq22510 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22510 eq22529
  have eq22552 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq22545
  have eq22559 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq22544
       grind)
    | exact superpose eq22544 eq41
    | exact resolve eq41 eq22544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22544
  have eq22563 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22559
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22559
    | exact resolve eq22559 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22559
  have eq22569 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22563
    | exact resolve eq22563 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22563
  have eq22585 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1127 x X0
       have i₂ := eq22552
       grind)
    | exact superpose eq22552 eq1127
    | (have j0 := eq1127 x X0
       grind)
    | exact resolve eq1127 eq22552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22552
  have eq22598 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22585 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22585
  have eq22606 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22598 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22598
    | (have j0 := eq22598 X0
       grind)
    | exact resolve eq22598 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22598
  have eq22765 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22606 eq26
    | (have j1 := eq22606 (σ y)
       grind)
    | exact resolve eq26 eq22606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22606
  have eq22797 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20707 eq22765
    | exact resolve eq22765 eq20707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20707 eq22765
  have eq22818 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22797 eq22569
    | exact resolve eq22569 eq22797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22569 eq22797
  have eq22823 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22818
  have eq22840 : x = (M.op x y) := by
    first
    | (have r₁ := eq22823
       have r₂ := eq20710
       grind)
    | exact resolve eq22823 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20710 eq22823
  have eq22853 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22840
       grind)
    | exact superpose eq22840 eq18
    | exact resolve eq18 eq22840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22854 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq22840
       grind)
    | exact superpose eq22840 eq22
    | exact resolve eq22 eq22840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq22892 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22854 eq20
    | exact resolve eq20 eq22854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22854
  have eq45149 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21941 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) x
       have r₂ := eq21941
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq21941
       grind)
    | (have r₁ := eq14 (M.op x y) x
       have r₂ := eq21941
       grind)
    | exact resolve eq14 eq21941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45150 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq45149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45149
  have eq174238 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45150 eq21941
    | exact resolve eq21941 eq45150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21941 eq45150
  have eq174251 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq174238
  have eq174269 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq174251 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq174251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174251
  have eq174284 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq174269
  have eq174291 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32 eq174284
    | exact resolve eq174284 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq174284
  have eq174341 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq174291 eq14
    | (have j0 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq14 (σ x) x
       have r₂ := eq174291
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq174291
       grind)
    | (have r₁ := eq14 (M.op x y) x
       have r₂ := eq174291
       grind)
    | exact resolve eq14 eq174291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174342 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq174341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174341
  have eq174702 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq174342 eq174291
    | exact resolve eq174291 eq174342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174291 eq174342
  have eq174711 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq174702
  have eq174831 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq174711 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq174711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq174833 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq174711 eq1128
    | (have j0 := eq1128 (σ x) X0
       grind)
    | exact resolve eq1128 eq174711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq174835 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq174711 eq1130
    | (have j0 := eq1130 (σ x) X0
       grind)
    | exact resolve eq1130 eq174711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq174711
  have eq174842 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq174835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174835
  have eq174844 : ∀ X0 : G, (k (τ (σ x)) X0) = (M.op (τ (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq174833 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174833
  have eq174846 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq174831
  have eq174851 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq174842
    | exact resolve eq174842 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174842
  have eq174852 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq174844
    | exact resolve eq174844 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174844
  have eq174853 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq174846
    | exact resolve eq174846 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq174846
  have eq174876 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq174851 X0
       have i₂ := eq22840
       grind)
    | exact superpose eq22840 eq174851
    | exact resolve eq174851 eq22840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174851
  have eq174877 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq174852 X0
       have i₂ := eq22840
       grind)
    | exact superpose eq22840 eq174852
    | exact resolve eq174852 eq22840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174852
  have eq174878 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq174853
       have i₂ := eq22840
       grind)
    | exact superpose eq22840 eq174853
    | exact resolve eq174853 eq22840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22840 eq174853
  have eq174879 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq174878
  have eq174902 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq174876 X0
       have j1 := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq174876 X0
       have r₂ := eq28 X0 y
       grind)
    | (have r₁ := eq174876 X0
       have r₂ := eq28 X0 (M.op x y)
       grind)
    | exact resolve eq174876 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174876
  have eq174903 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq174877 X0
       have j1 := eq14 (M.op x y) X0
       grind)
    | (have r₁ := eq174877 X0
       have r₂ := eq14 y x
       grind)
    | (have r₁ := eq174877 X0
       have r₂ := eq14 (M.op x y) x
       grind)
    | exact resolve eq174877 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174877
  have eq174924 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq174902 eq174879
    | exact resolve eq174879 eq174902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174879 eq174902
  have eq174925 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq174924
  have eq174956 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq174925 eq1127
    | (have j0 := eq1127 (M.op x y) X0
       grind)
    | exact resolve eq1127 eq174925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq174925
  have eq174969 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq174956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174956
  have eq174977 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20 eq174969
    | (have j0 := eq174969 X0
       grind)
    | exact resolve eq174969 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174969
  have eq175004 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22892 eq174977
    | exact resolve eq174977 eq22892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174977
  have eq175209 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq174903 eq22853
    | exact resolve eq22853 eq174903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174903
  have eq175240 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq175209 eq41
    | exact resolve eq41 eq175209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175209
  have eq175247 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq175240
    | exact resolve eq175240 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175240
  have eq175269 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22892 eq175247
    | exact resolve eq175247 eq22892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175247
  have eq176640 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq175004 eq26
    | (have j1 := eq175004 (σ y)
       grind)
    | exact resolve eq26 eq175004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175004
  have eq176678 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq175269 eq176640
    | exact resolve eq176640 eq175269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175269 eq176640
  have eq176679 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq176678
  have eq176707 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq176679
       grind)
    | exact superpose eq176679 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq176679
       grind)
    | exact resolve eq28 eq176679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq176708 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq176679
       grind)
    | exact superpose eq176679 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq176679
       grind)
    | exact resolve eq14 eq176679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176709 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq176708 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176708
  have eq176710 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq176707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176707
  have eq176731 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq176679
       have i₂ := eq176709 y
       grind)
    | exact superpose eq176709 eq176679
    | exact resolve eq176679 eq176709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176679 eq176709
  have eq176743 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq176731
  have eq176763 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1129 y X0
       have i₂ := eq176743
       grind)
    | exact superpose eq176743 eq1129
    | (have j0 := eq1129 y X0
       grind)
    | exact resolve eq1129 eq176743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq176743
  have eq176772 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq176763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176763
  have eq176781 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq176772 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq176772
    | (have j0 := eq176772 X0
       grind)
    | exact resolve eq176772 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq176772
  have eq176906 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22853
       have i₂ := eq176710 sF0
       grind)
    | exact superpose eq176710 eq22853
    | exact resolve eq22853 eq176710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22853 eq176710
  have eq176937 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176906 eq41
    | exact resolve eq41 eq176906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq176906
  have eq176943 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq176937
    | exact resolve eq176937 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq176937
  have eq176965 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22892 eq176943
    | exact resolve eq176943 eq22892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176943
  have eq177126 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176781 eq26
    | (have j1 := eq176781 (σ x)
       grind)
    | exact resolve eq26 eq176781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq176781
  have eq177142 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176965 eq177126
    | exact resolve eq177126 eq176965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176965 eq177126
  have eq177143 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177142
  have eq177147 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq177143 eq27
    | exact resolve eq27 eq177143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq177143
  have eq177149 : False := by grind
  exact eq177149

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pyy_y_x_y_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq30 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq45
  have eq61 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    first
    | (have j0 := eq29 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq29 x
       have r₂ := eq14 x X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq10
    | exact resolve eq10 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq51
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq51
    | exact resolve eq51 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq61 sF3
       grind)
    | exact superpose eq61 eq84
    | exact resolve eq84 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq86
    | exact resolve eq86 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq86
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq118 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq419 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq72
    | (have j0 := eq72 X1 (σ X0)
       grind)
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq15933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq15934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq15933
    | exact resolve eq15933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15933
  have eq15945 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq15934
       have r₂ := eq28
       grind)
    | exact resolve eq15934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15934
  have eq15951 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq15945 eq118
    | exact resolve eq118 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq15945
  have eq15972 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq15951
    | exact resolve eq15951 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951
  have eq15973 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq15972
  have eq15978 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15973 eq66
    | exact resolve eq66 eq15973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq16003 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq30 eq15978
    | exact resolve eq15978 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq16004 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16003
  have eq16018 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq419 y X0
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq419
    | (have j0 := eq419 y X0
       grind)
    | exact resolve eq419 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq16019 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq72 X0 y
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq72
    | (have j0 := eq72 X0 y
       grind)
    | (have r₁ := eq72 X0 y
       have r₂ := eq16004
       grind)
    | (have r₁ := eq72 X0 x
       have r₂ := eq16004
       grind)
    | exact resolve eq72 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq16004
  have eq16022 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16019 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq16023 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16018
  have eq16025 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16023 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16023
    | (have j0 := eq16023 X0
       grind)
    | exact resolve eq16023 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16023
  have eq16152 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq16022 x
       grind)
    | exact superpose eq16022 eq46
    | exact resolve eq46 eq16022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16022
  have eq16214 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16152
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16152
    | exact resolve eq16152 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16152
  have eq16224 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq16214
    | exact resolve eq16214 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16214
  have eq16316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16025 eq16224
    | exact resolve eq16224 eq16025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16025 eq16224
  have eq16340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16316
  have eq16353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16340
    | exact resolve eq16340 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16340
  have eq16364 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16353
       have r₂ := eq28
       grind)
    | exact resolve eq16353 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16353
  have eq16376 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq420 x X0
       have i₂ := eq16364
       grind)
    | exact superpose eq16364 eq420
    | (have j0 := eq420 x X0
       grind)
    | exact resolve eq420 eq16364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq16379 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq16364
       grind)
    | exact superpose eq16364 eq14
    | (have j0 := eq14 x X0
       grind)
    | (have r₁ := eq14 x x
       have r₂ := eq16364
       grind)
    | exact resolve eq14 eq16364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16364
  have eq16380 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16379
  have eq16383 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376
  have eq16385 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16383 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16383
    | (have j0 := eq16383 X0
       grind)
    | exact resolve eq16383 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16383
  have eq16710 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq16380 y
       grind)
    | exact superpose eq16380 eq46
    | exact resolve eq46 eq16380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16380
  have eq16742 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16710
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16710
    | exact resolve eq16710 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16710
  have eq16763 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq16742
    | exact resolve eq16742 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16742
  have eq17280 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16385 eq16763
    | exact resolve eq16763 eq16385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16385 eq16763
  have eq17281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17280
  have eq17285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17281
    | exact resolve eq17281 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17281
  have eq17308 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17285
       have r₂ := eq28
       grind)
    | exact resolve eq17285 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17285
  have eq17556 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17308 eq31
    | exact resolve eq31 eq17308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17308
  have eq17680 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq17556
    | exact resolve eq17556 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17556
  have eq17681 : x = y := by grind
  clear eq17680
  have eq17700 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17681
       grind)
    | exact superpose eq17681 eq19
    | exact resolve eq19 eq17681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17701 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17681
       grind)
    | exact superpose eq17681 eq25
    | exact resolve eq25 eq17681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17681
  have eq17834 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17701
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17701
    | exact resolve eq17701 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17701
  have eq17855 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17834 eq27
    | exact resolve eq27 eq17834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17834
  have eq18481 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17855 eq66
    | exact resolve eq66 eq17855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq17855
  have eq18504 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18481
       have i₂ := eq17700
       grind)
    | exact superpose eq17700 eq18481
    | exact resolve eq18481 eq17700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17700 eq18481
  have eq18511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18504 eq15
    | exact resolve eq15 eq18504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18504
  have eq18600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18511
    | exact resolve eq18511 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18511
  have eq18622 : False := by grind
  exact eq18622
