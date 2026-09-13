import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = X then X else if X = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_pyx_x_x_y_pxx_x_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq10
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq66 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq51 sF2
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq68
    | exact resolve eq68 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq91
    | exact resolve eq91 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq51 y
       grind)
    | exact superpose eq51 eq95
    | exact resolve eq95 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq119 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq185 : (σ (k (M.op y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq41
    | exact resolve eq41 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq318 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq474 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq318 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq318
    | (have j0 := eq318 X0 y
       grind)
    | exact resolve eq318 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq526 : (k (M.op y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq119 eq474
    | exact resolve eq474 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq566 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq75
  have eq690 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq566 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq566 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq4821 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4852 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4821
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4821
    | exact resolve eq4821 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821
  have eq4943 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4852
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq4852
    | exact resolve eq4852 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852
  have eq5027 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4943
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4943
    | exact resolve eq4943 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943
  have eq5111 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5027
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5027
    | exact resolve eq5027 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5027
  have eq5194 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5111
    | exact resolve eq5111 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5277 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5194
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5194
    | exact resolve eq5194 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194
  have eq5359 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5277
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5277
    | exact resolve eq5277 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5277
  have eq5440 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5359
    | exact resolve eq5359 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359
  have eq5472 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5440
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5440
    | exact resolve eq5440 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5440
  have eq5480 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5472
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5472
    | exact resolve eq5472 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5472
  have eq16632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16632
    | exact resolve eq16632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16632
  have eq16644 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq16633
       have r₂ := eq28
       grind)
    | exact resolve eq16633 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16633
  have eq16648 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16644
    | exact resolve eq16644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16644
  have eq16650 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16648
    | exact resolve eq16648 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16648
  have eq16661 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16650 eq14
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq16650
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq16650
       grind)
    | exact resolve eq14 eq16650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16650
  have eq17211 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16661
    | (have j0 := eq16661 (σ x)
       grind)
    | (have r₁ := eq16661 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq16661 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16661
  have eq17215 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq17211
  have eq17223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17215 eq108
    | exact resolve eq108 eq17215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17215
  have eq17234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17223
  have eq17237 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17234
       have r₂ := eq28
       grind)
    | exact resolve eq17234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17234
  have eq17312 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq17237
       grind)
    | exact superpose eq17237 eq97
    | exact resolve eq97 eq17237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17322 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq17237
       grind)
    | exact superpose eq17237 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq17237
       grind)
    | exact resolve eq14 eq17237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17336 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17312
    | exact resolve eq17312 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17312
  have eq18059 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17322 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17322
    | (have j0 := eq17322 x
       grind)
    | (have r₁ := eq17322 x
       have r₂ := eq19
       grind)
    | exact resolve eq17322 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17322
  have eq18065 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18059
  have eq18080 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq690 x y
       have i₂ := eq18065
       grind)
    | exact superpose eq18065 eq690
    | (have j0 := eq690 x y
       grind)
    | exact resolve eq690 eq18065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq18065
  have eq18086 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18080
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18080
    | exact resolve eq18080 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18080
  have eq18098 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18086
    | exact resolve eq18086 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18086
  have eq18102 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18098
       have r₂ := eq17336
       grind)
    | exact resolve eq18098 eq17336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18098
  have eq18104 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18102
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18102
    | exact resolve eq18102 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18102
  have eq18106 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18104
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18104
    | exact resolve eq18104 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18104
  have eq18108 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18106
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18106
    | exact resolve eq18106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18106
  have eq18110 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18108
    | exact resolve eq18108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18108
  have eq18112 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18110
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18110
    | exact resolve eq18110 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18110
  have eq18115 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18112
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18112
    | exact resolve eq18112 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18112
  have eq18117 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18115
    | exact resolve eq18115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18115
  have eq18118 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18117
  have eq18121 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18118
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18118
    | exact resolve eq18118 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18122 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18121
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18121
    | exact resolve eq18121 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18121
  have eq18123 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq18122
  have eq18186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18123 eq17336
    | exact resolve eq17336 eq18123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17336 eq18123
  have eq18197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18186
  have eq18204 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18197
       have r₂ := eq28
       grind)
    | exact resolve eq18197 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18197
  have eq18206 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18204 eq67
    | (have r₁ := eq67
       have r₂ := eq18204
       grind)
    | exact resolve eq67 eq18204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq18207 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18204 eq28
    | exact resolve eq28 eq18204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18204
  have eq18208 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq18206
  have eq19206 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18208 eq104
    | exact resolve eq104 eq18208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq19207 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18208 eq108
    | exact resolve eq108 eq18208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18208
  have eq19228 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq19207
  have eq19242 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19228
       have r₂ := eq18207
       grind)
    | exact resolve eq19228 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19228
  have eq19243 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq19206
    | exact resolve eq19206 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19206
  have eq19261 : (k (M.op y y) y) = (τ (k (σ y) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19242 eq526
    | exact resolve eq526 eq19242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq19279 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq19242 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq19242
       grind)
    | exact resolve eq14 eq19242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19242
  have eq19304 : (τ (M.op (σ y) (σ y))) = (k (M.op y y) y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19261
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq19261
    | exact resolve eq19261 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19261
  have eq19312 : (M.op y y) = (k (M.op y y) y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq119 eq19304
    | exact resolve eq19304 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19304
  have eq19319 : (τ (σ y)) = (M.op y y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19243 eq119
    | exact resolve eq119 eq19243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19372 : y = (k y x) ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq19319
    | exact resolve eq19319 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19319
  have eq24041 : (σ (M.op y y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq19312
       grind)
    | exact superpose eq19312 eq185
    | exact resolve eq185 eq19312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq19312
  have eq24053 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24041
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq24041
    | exact resolve eq24041 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24041
  have eq27184 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19243 eq24053
    | exact resolve eq24053 eq19243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24053
  have eq27212 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq27184
  have eq27216 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq27212
       have r₂ := eq66
       grind)
    | exact resolve eq27212 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27212
  have eq27217 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq27216
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq27216
    | exact resolve eq27216 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq27216
  have eq27474 : (τ (σ y)) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq27217 eq119
    | exact resolve eq119 eq27217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq27217
  have eq27545 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq27474
    | exact resolve eq27474 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27474
  have eq27951 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq27545
  have eq27964 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq27951
       have r₂ := eq19372
       grind)
    | exact resolve eq27951 eq19372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19372 eq27951
  have eq27995 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq27964
       grind)
    | exact superpose eq27964 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq27964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq27964
  have eq27998 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq27995
  have eq28006 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27998
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq27998
    | exact resolve eq27998 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27998
  have eq28020 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28006
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28006
    | exact resolve eq28006 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28006
  have eq28025 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28020
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28020
    | exact resolve eq28020 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28020
  have eq28027 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq28025
    | exact resolve eq28025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28025
  have eq28029 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28027
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28027
    | exact resolve eq28027 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28027
  have eq28031 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28029
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28029
    | exact resolve eq28029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28029
  have eq28033 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq28031
    | exact resolve eq28031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28031
  have eq28035 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28033
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28033
    | exact resolve eq28033 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28033
  have eq28037 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28035
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28035
    | exact resolve eq28035 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28035
  have eq28038 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq28037
  have eq48129 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19279
    | (have j0 := eq19279 (σ x)
       grind)
    | exact resolve eq19279 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19279
  have eq48154 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48129
       have r₂ := eq17237
       grind)
    | exact resolve eq48129 eq17237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17237 eq48129
  have eq48167 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48154 eq108
    | exact resolve eq108 eq48154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq48154
  have eq48210 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq48167
  have eq48224 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48210
       have r₂ := eq18207
       grind)
    | exact resolve eq48210 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48210
  have eq48235 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq48224
       grind)
    | exact superpose eq48224 eq97
    | exact resolve eq97 eq48224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48260 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq48224
       grind)
    | exact superpose eq48224 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq48224
       grind)
    | exact resolve eq14 eq48224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48224
  have eq48293 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq48235
    | exact resolve eq48235 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48235
  have eq48578 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48293 eq19243
    | exact resolve eq19243 eq48293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19243 eq48293
  have eq48634 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq48578
  have eq48656 : y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48634
       have r₂ := eq18207
       grind)
    | exact resolve eq48634 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18207 eq48634
  have eq51988 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48260 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48260
    | (have j0 := eq48260 x
       grind)
    | (have r₁ := eq48260 x
       have r₂ := eq19
       grind)
    | exact resolve eq48260 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48260
  have eq52011 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51988
  have eq52060 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48656
       have i₂ := eq52011
       grind)
    | exact superpose eq52011 eq48656
    | exact resolve eq48656 eq52011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48656 eq52011
  have eq52077 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq52060
  have eq52145 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq52077 eq30
    | exact resolve eq30 eq52077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq52077
  have eq52269 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq52145
    | exact resolve eq52145 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52145
  have eq52270 : y = (M.op x y) ∨ x = y := by grind
  clear eq52269
  have eq52289 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq52270 eq21
    | exact resolve eq21 eq52270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52292 : y ≠ y ∨ y = (M.op y y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq52270 eq66
    | (have r₁ := eq66
       have r₂ := eq52270
       grind)
    | exact resolve eq66 eq52270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq52297 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq52270 eq120
    | exact resolve eq120 eq52270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq52418 : y = (k y x) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq52292
  have eq52527 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52297 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq52297
    | exact resolve eq52297 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq52297
  have eq52534 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52289
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52289
    | exact resolve eq52289 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52289
  have eq52560 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52534 eq27
    | exact resolve eq27 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52625 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq52534 eq5480
    | exact resolve eq5480 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5480
  have eq52699 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq52534 eq28038
    | exact resolve eq28038 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28038
  have eq52782 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq52699
  have eq52865 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq52782
       have r₂ := eq28
       grind)
    | exact resolve eq52782 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52782
  have eq52875 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq52625
       have r₂ := eq28
       grind)
    | exact resolve eq52625 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52625
  have eq52959 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52560 eq14
    | (have j0 := eq14 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq14 eq52560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52560
  have eq80623 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq52418
       grind)
    | exact superpose eq52418 eq90
    | exact resolve eq90 eq52418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52418
  have eq80687 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq80623
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80623
    | exact resolve eq80623 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80623
  have eq80710 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq52534 eq80687
    | exact resolve eq80687 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80687
  have eq80788 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq80710
  have eq410709 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq52865 eq52959
    | (have r₁ := eq52959
       have r₂ := eq52865
       grind)
    | exact resolve eq52959 eq52865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52865 eq52959
  have eq410737 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq410709
  have eq410738 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq410737
  have eq879108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq410738 eq80788
    | exact resolve eq80788 eq410738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80788 eq410738
  have eq879149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq879108
  have eq879161 : y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq879149
       have r₂ := eq28
       grind)
    | exact resolve eq879149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879149
  have eq879173 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq879161
       grind)
    | exact superpose eq879161 eq97
    | exact resolve eq97 eq879161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq879238 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq879161
       grind)
    | exact superpose eq879161 eq14
    | exact resolve eq14 eq879161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879161
  have eq879318 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq879173
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq879173
    | exact resolve eq879173 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879173
  have eq879323 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq52534 eq879318
    | exact resolve eq879318 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879318
  have eq879551 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq879323
  have eq3320774 : y ≠ (M.op x y) ∨ y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq879238 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq879238
    | (have j0 := eq879238 x
       grind)
    | exact resolve eq879238 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879238
  have eq3320810 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3320774
       have r₂ := eq52270
       grind)
    | exact resolve eq3320774 eq52270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320774
  have eq3320823 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq3320810
       grind)
    | exact superpose eq3320810 eq90
    | exact resolve eq90 eq3320810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3320810
  have eq3321509 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3320823
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3320823
    | exact resolve eq3320823 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320823
  have eq3321756 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3321509 eq52527
    | exact resolve eq52527 eq3321509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52527 eq3321509
  have eq3321877 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3321756
  have eq3322101 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3321877 eq52875
    | exact resolve eq52875 eq3321877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52875 eq3321877
  have eq3322158 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq3322101
  have eq3322181 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3322158
       have r₂ := eq52534
       grind)
    | exact resolve eq3322158 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52534 eq3322158
  have eq3323478 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq3322181 eq879551
    | exact resolve eq879551 eq3322181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879551 eq3322181
  have eq3323531 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3323478
  have eq3323577 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3323531
       have r₂ := eq28
       grind)
    | exact resolve eq3323531 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323531
  have eq3323581 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3323577 eq29
    | exact resolve eq29 eq3323577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3323577
  have eq3324608 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq3323581
    | exact resolve eq3323581 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3323581
  have eq3326200 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3324608 eq52270
    | exact resolve eq52270 eq3324608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52270 eq3324608
  have eq3328685 : x = y := by grind
  clear eq3326200
  have eq3330781 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3328685
       grind)
    | exact superpose eq3328685 eq19
    | exact resolve eq19 eq3328685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3330782 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3328685
       grind)
    | exact superpose eq3328685 eq25
    | exact resolve eq25 eq3328685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3328685
  have eq3333672 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3330782
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3330782
    | exact resolve eq3330782 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3330782
  have eq3334240 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3333672 eq27
    | exact resolve eq27 eq3333672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3333672
  have eq3337432 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3334240 eq69
    | exact resolve eq69 eq3334240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3334240
  have eq3337524 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3337432
       have i₂ := eq3330781
       grind)
    | exact superpose eq3330781 eq3337432
    | exact resolve eq3337432 eq3330781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330781 eq3337432
  have eq3337595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3337524 eq15
    | exact resolve eq15 eq3337524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337524
  have eq3338490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq3337595
    | exact resolve eq3337595 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3337595
  have eq3338732 : False := by grind
  exact eq3338732

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = X then X else if X = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_pyx_x_x_y_pxx_x_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq10
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq66 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq51 sF2
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq68
    | exact resolve eq68 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq91
    | exact resolve eq91 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq51 y
       grind)
    | exact superpose eq51 eq95
    | exact resolve eq95 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq119 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq185 : (σ (k (M.op y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq41
    | exact resolve eq41 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq318 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq474 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq318 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq318
    | (have j0 := eq318 X0 y
       grind)
    | exact resolve eq318 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq526 : (k (M.op y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq119 eq474
    | exact resolve eq474 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq566 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq75
  have eq690 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq566 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq566 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq4821 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4852 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4821
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4821
    | exact resolve eq4821 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821
  have eq4943 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4852
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq4852
    | exact resolve eq4852 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852
  have eq5027 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4943
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4943
    | exact resolve eq4943 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943
  have eq5111 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5027
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5027
    | exact resolve eq5027 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5027
  have eq5194 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5111
    | exact resolve eq5111 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5277 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5194
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5194
    | exact resolve eq5194 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194
  have eq5359 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5277
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5277
    | exact resolve eq5277 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5277
  have eq5440 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5359
    | exact resolve eq5359 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359
  have eq5472 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5440
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5440
    | exact resolve eq5440 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5440
  have eq5480 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5472
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5472
    | exact resolve eq5472 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5472
  have eq16632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16632
    | exact resolve eq16632 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16632
  have eq16644 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq16633
       have r₂ := eq28
       grind)
    | exact resolve eq16633 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16633
  have eq16648 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16644
    | exact resolve eq16644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16644
  have eq16650 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16648
    | exact resolve eq16648 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16648
  have eq16661 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16650 eq14
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq16650
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq16650
       grind)
    | exact resolve eq14 eq16650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16650
  have eq17211 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16661
    | (have j0 := eq16661 (σ x)
       grind)
    | (have r₁ := eq16661 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq16661 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16661
  have eq17215 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq17211
  have eq17223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17215 eq108
    | exact resolve eq108 eq17215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17215
  have eq17234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17223
  have eq17237 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17234
       have r₂ := eq28
       grind)
    | exact resolve eq17234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17234
  have eq17312 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq17237
       grind)
    | exact superpose eq17237 eq97
    | exact resolve eq97 eq17237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17322 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq17237
       grind)
    | exact superpose eq17237 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq17237
       grind)
    | exact resolve eq14 eq17237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17336 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17312
    | exact resolve eq17312 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17312
  have eq18059 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17322 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17322
    | (have j0 := eq17322 x
       grind)
    | (have r₁ := eq17322 x
       have r₂ := eq19
       grind)
    | exact resolve eq17322 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17322
  have eq18065 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18059
  have eq18080 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq690 x y
       have i₂ := eq18065
       grind)
    | exact superpose eq18065 eq690
    | (have j0 := eq690 x y
       grind)
    | exact resolve eq690 eq18065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq18065
  have eq18086 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18080
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18080
    | exact resolve eq18080 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18080
  have eq18098 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18086
    | exact resolve eq18086 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18086
  have eq18102 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18098
       have r₂ := eq17336
       grind)
    | exact resolve eq18098 eq17336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18098
  have eq18104 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18102
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18102
    | exact resolve eq18102 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18102
  have eq18106 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18104
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18104
    | exact resolve eq18104 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18104
  have eq18108 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18106
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18106
    | exact resolve eq18106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18106
  have eq18110 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18108
    | exact resolve eq18108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18108
  have eq18112 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18110
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18110
    | exact resolve eq18110 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18110
  have eq18115 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18112
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18112
    | exact resolve eq18112 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18112
  have eq18117 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18115
    | exact resolve eq18115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18115
  have eq18118 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18117
  have eq18121 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18118
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18118
    | exact resolve eq18118 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18122 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18121
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18121
    | exact resolve eq18121 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18121
  have eq18123 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq18122
  have eq18186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18123 eq17336
    | exact resolve eq17336 eq18123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17336 eq18123
  have eq18197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18186
  have eq18204 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18197
       have r₂ := eq28
       grind)
    | exact resolve eq18197 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18197
  have eq18206 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18204 eq67
    | (have r₁ := eq67
       have r₂ := eq18204
       grind)
    | exact resolve eq67 eq18204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq18207 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18204 eq28
    | exact resolve eq28 eq18204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18204
  have eq18208 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq18206
  have eq19206 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18208 eq104
    | exact resolve eq104 eq18208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq19207 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18208 eq108
    | exact resolve eq108 eq18208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18208
  have eq19228 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq19207
  have eq19242 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19228
       have r₂ := eq18207
       grind)
    | exact resolve eq19228 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19228
  have eq19243 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq19206
    | exact resolve eq19206 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19206
  have eq19261 : (k (M.op y y) y) = (τ (k (σ y) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19242 eq526
    | exact resolve eq526 eq19242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq19279 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq19242 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq19242
       grind)
    | exact resolve eq14 eq19242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19242
  have eq19304 : (τ (M.op (σ y) (σ y))) = (k (M.op y y) y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19261
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq19261
    | exact resolve eq19261 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19261
  have eq19312 : (M.op y y) = (k (M.op y y) y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq119 eq19304
    | exact resolve eq19304 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19304
  have eq19319 : (τ (σ y)) = (M.op y y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19243 eq119
    | exact resolve eq119 eq19243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19372 : y = (k y x) ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq19319
    | exact resolve eq19319 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19319
  have eq24041 : (σ (M.op y y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq19312
       grind)
    | exact superpose eq19312 eq185
    | exact resolve eq185 eq19312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq19312
  have eq24053 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24041
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq24041
    | exact resolve eq24041 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24041
  have eq27184 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19243 eq24053
    | exact resolve eq24053 eq19243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24053
  have eq27212 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq27184
  have eq27216 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq27212
       have r₂ := eq66
       grind)
    | exact resolve eq27212 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27212
  have eq27217 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq27216
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq27216
    | exact resolve eq27216 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq27216
  have eq27474 : (τ (σ y)) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq27217 eq119
    | exact resolve eq119 eq27217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq27217
  have eq27545 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq27474
    | exact resolve eq27474 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27474
  have eq27951 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq27545
  have eq27964 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq27951
       have r₂ := eq19372
       grind)
    | exact resolve eq27951 eq19372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19372 eq27951
  have eq27995 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq27964
       grind)
    | exact superpose eq27964 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq27964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq27964
  have eq27998 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq27995
  have eq28006 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27998
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq27998
    | exact resolve eq27998 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27998
  have eq28020 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28006
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28006
    | exact resolve eq28006 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28006
  have eq28025 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28020
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28020
    | exact resolve eq28020 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28020
  have eq28027 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq28025
    | exact resolve eq28025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28025
  have eq28029 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28027
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28027
    | exact resolve eq28027 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28027
  have eq28031 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28029
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28029
    | exact resolve eq28029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28029
  have eq28033 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq28031
    | exact resolve eq28031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28031
  have eq28035 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28033
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28033
    | exact resolve eq28033 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28033
  have eq28037 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28035
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28035
    | exact resolve eq28035 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28035
  have eq28038 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq28037
  have eq48129 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19279
    | (have j0 := eq19279 (σ x)
       grind)
    | exact resolve eq19279 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19279
  have eq48154 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48129
       have r₂ := eq17237
       grind)
    | exact resolve eq48129 eq17237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17237 eq48129
  have eq48167 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48154 eq108
    | exact resolve eq108 eq48154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq48154
  have eq48210 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq48167
  have eq48224 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48210
       have r₂ := eq18207
       grind)
    | exact resolve eq48210 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48210
  have eq48235 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq48224
       grind)
    | exact superpose eq48224 eq97
    | exact resolve eq97 eq48224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48260 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq48224
       grind)
    | exact superpose eq48224 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq48224
       grind)
    | exact resolve eq14 eq48224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48224
  have eq48293 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq48235
    | exact resolve eq48235 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48235
  have eq48578 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48293 eq19243
    | exact resolve eq19243 eq48293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19243 eq48293
  have eq48634 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq48578
  have eq48656 : y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48634
       have r₂ := eq18207
       grind)
    | exact resolve eq48634 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18207 eq48634
  have eq51988 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48260 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48260
    | (have j0 := eq48260 x
       grind)
    | (have r₁ := eq48260 x
       have r₂ := eq19
       grind)
    | exact resolve eq48260 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48260
  have eq52011 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51988
  have eq52060 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48656
       have i₂ := eq52011
       grind)
    | exact superpose eq52011 eq48656
    | exact resolve eq48656 eq52011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48656 eq52011
  have eq52077 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq52060
  have eq52145 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq52077 eq30
    | exact resolve eq30 eq52077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq52077
  have eq52269 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq52145
    | exact resolve eq52145 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52145
  have eq52270 : y = (M.op x y) ∨ x = y := by grind
  clear eq52269
  have eq52289 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq52270 eq21
    | exact resolve eq21 eq52270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52292 : y ≠ y ∨ y = (M.op y y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq52270 eq66
    | (have r₁ := eq66
       have r₂ := eq52270
       grind)
    | exact resolve eq66 eq52270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq52297 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq52270 eq120
    | exact resolve eq120 eq52270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq52418 : y = (k y x) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq52292
  have eq52527 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52297 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq52297
    | exact resolve eq52297 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq52297
  have eq52534 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52289
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52289
    | exact resolve eq52289 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52289
  have eq52560 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52534 eq27
    | exact resolve eq27 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52625 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq52534 eq5480
    | exact resolve eq5480 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5480
  have eq52699 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq52534 eq28038
    | exact resolve eq28038 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28038
  have eq52782 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq52699
  have eq52865 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq52782
       have r₂ := eq28
       grind)
    | exact resolve eq52782 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52782
  have eq52875 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq52625
       have r₂ := eq28
       grind)
    | exact resolve eq52625 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52625
  have eq52959 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52560 eq14
    | (have j0 := eq14 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq14 eq52560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52560
  have eq80623 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq52418
       grind)
    | exact superpose eq52418 eq90
    | exact resolve eq90 eq52418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52418
  have eq80687 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq80623
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80623
    | exact resolve eq80623 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80623
  have eq80710 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq52534 eq80687
    | exact resolve eq80687 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80687
  have eq80788 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq80710
  have eq410709 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq52865 eq52959
    | (have r₁ := eq52959
       have r₂ := eq52865
       grind)
    | exact resolve eq52959 eq52865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52865 eq52959
  have eq410737 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq410709
  have eq410738 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq410737
  have eq879108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq410738 eq80788
    | exact resolve eq80788 eq410738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80788 eq410738
  have eq879149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq879108
  have eq879161 : y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq879149
       have r₂ := eq28
       grind)
    | exact resolve eq879149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879149
  have eq879173 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq879161
       grind)
    | exact superpose eq879161 eq97
    | exact resolve eq97 eq879161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq879238 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq879161
       grind)
    | exact superpose eq879161 eq14
    | exact resolve eq14 eq879161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879161
  have eq879318 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq879173
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq879173
    | exact resolve eq879173 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879173
  have eq879323 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq52534 eq879318
    | exact resolve eq879318 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879318
  have eq879551 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq879323
  have eq3320774 : y ≠ (M.op x y) ∨ y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq879238 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq879238
    | (have j0 := eq879238 x
       grind)
    | exact resolve eq879238 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879238
  have eq3320810 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3320774
       have r₂ := eq52270
       grind)
    | exact resolve eq3320774 eq52270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320774
  have eq3320823 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq3320810
       grind)
    | exact superpose eq3320810 eq90
    | exact resolve eq90 eq3320810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3320810
  have eq3321509 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3320823
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3320823
    | exact resolve eq3320823 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320823
  have eq3321756 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3321509 eq52527
    | exact resolve eq52527 eq3321509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52527 eq3321509
  have eq3321877 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3321756
  have eq3322101 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3321877 eq52875
    | exact resolve eq52875 eq3321877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52875 eq3321877
  have eq3322158 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq3322101
  have eq3322181 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3322158
       have r₂ := eq52534
       grind)
    | exact resolve eq3322158 eq52534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52534 eq3322158
  have eq3323478 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq3322181 eq879551
    | exact resolve eq879551 eq3322181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879551 eq3322181
  have eq3323531 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3323478
  have eq3323577 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3323531
       have r₂ := eq28
       grind)
    | exact resolve eq3323531 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323531
  have eq3323581 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3323577 eq29
    | exact resolve eq29 eq3323577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3323577
  have eq3324608 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq3323581
    | exact resolve eq3323581 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3323581
  have eq3326200 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3324608 eq52270
    | exact resolve eq52270 eq3324608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52270 eq3324608
  have eq3328685 : x = y := by grind
  clear eq3326200
  have eq3330781 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3328685
       grind)
    | exact superpose eq3328685 eq19
    | exact resolve eq19 eq3328685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3330782 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3328685
       grind)
    | exact superpose eq3328685 eq25
    | exact resolve eq25 eq3328685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3328685
  have eq3333672 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3330782
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3330782
    | exact resolve eq3330782 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3330782
  have eq3334240 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3333672 eq27
    | exact resolve eq27 eq3333672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3333672
  have eq3337432 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3334240 eq69
    | exact resolve eq69 eq3334240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3334240
  have eq3337524 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3337432
       have i₂ := eq3330781
       grind)
    | exact superpose eq3330781 eq3337432
    | exact resolve eq3337432 eq3330781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330781 eq3337432
  have eq3337595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3337524 eq15
    | exact resolve eq15 eq3337524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337524
  have eq3338490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq3337595
    | exact resolve eq3337595 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3337595
  have eq3338732 : False := by grind
  exact eq3338732

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_x_y_pyx_x_pxx_x_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq10
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq66 : y ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ y = (k y x) := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq51 sF2
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq68
    | exact resolve eq68 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq91
    | exact resolve eq91 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq51 y
       grind)
    | exact superpose eq51 eq95
    | exact resolve eq95 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq119 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq185 : (σ (k (M.op y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq41
    | exact resolve eq41 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq318 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq474 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq318 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq318
    | (have j0 := eq318 X0 y
       grind)
    | exact resolve eq318 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq526 : (k (M.op y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq119 eq474
    | exact resolve eq474 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq566 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq75
  have eq690 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq566 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq566 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq4828 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4859 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4828
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4828
    | exact resolve eq4828 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828
  have eq4950 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4859
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq4859
    | exact resolve eq4859 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq5034 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4950
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4950
    | exact resolve eq4950 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950
  have eq5118 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5034
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5034
    | exact resolve eq5034 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034
  have eq5201 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq5118
    | exact resolve eq5118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5118
  have eq5284 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5201
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5201
    | exact resolve eq5201 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5201
  have eq5366 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5284
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5284
    | exact resolve eq5284 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5284
  have eq5447 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5366
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5366
    | exact resolve eq5366 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5366
  have eq5479 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5447
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5447
    | exact resolve eq5447 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447
  have eq5487 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq5479
    | exact resolve eq5479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5479
  have eq16643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16643
    | exact resolve eq16643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16643
  have eq16655 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq16644
       have r₂ := eq28
       grind)
    | exact resolve eq16644 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16644
  have eq16659 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16655
    | exact resolve eq16655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16655
  have eq16661 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16659
    | exact resolve eq16659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16659
  have eq16672 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16661 eq14
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq16661
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq16661
       grind)
    | exact resolve eq14 eq16661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16661
  have eq17222 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16672
    | (have j0 := eq16672 (σ x)
       grind)
    | (have r₁ := eq16672 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq16672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16672
  have eq17226 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq17222
  have eq17234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17226 eq108
    | exact resolve eq108 eq17226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17226
  have eq17245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17234
  have eq17248 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17245
       have r₂ := eq28
       grind)
    | exact resolve eq17245 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17245
  have eq17323 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq17248
       grind)
    | exact superpose eq17248 eq97
    | exact resolve eq97 eq17248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17333 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq17248
       grind)
    | exact superpose eq17248 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq17248
       grind)
    | exact resolve eq14 eq17248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17347 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17323
    | exact resolve eq17323 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323
  have eq18064 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17333 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17333
    | (have j0 := eq17333 x
       grind)
    | (have r₁ := eq17333 x
       have r₂ := eq19
       grind)
    | exact resolve eq17333 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17333
  have eq18070 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18064
  have eq18085 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq690 x y
       have i₂ := eq18070
       grind)
    | exact superpose eq18070 eq690
    | (have j0 := eq690 x y
       grind)
    | exact resolve eq690 eq18070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq18070
  have eq18091 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18085
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18085
    | exact resolve eq18085 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18085
  have eq18103 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18091
    | exact resolve eq18091 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18091
  have eq18107 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18103
       have r₂ := eq17347
       grind)
    | exact resolve eq18103 eq17347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18103
  have eq18109 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18107
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18107
    | exact resolve eq18107 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18107
  have eq18111 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18109
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18109
    | exact resolve eq18109 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18109
  have eq18113 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18111
    | exact resolve eq18111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18111
  have eq18115 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18113
    | exact resolve eq18113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18113
  have eq18118 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18115
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18115
    | exact resolve eq18115 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18115
  have eq18120 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18118
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18118
    | exact resolve eq18118 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18121 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18120
  have eq18123 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18121
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18121
    | exact resolve eq18121 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18121
  have eq18126 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18123
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18123
    | exact resolve eq18123 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq18127 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18126
    | exact resolve eq18126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18126
  have eq18128 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq18127
  have eq18191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18128 eq17347
    | exact resolve eq17347 eq18128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17347 eq18128
  have eq18202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18191
  have eq18209 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18202
       have r₂ := eq28
       grind)
    | exact resolve eq18202 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18202
  have eq18211 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18209 eq67
    | (have r₁ := eq67
       have r₂ := eq18209
       grind)
    | exact resolve eq67 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq18212 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18209 eq28
    | exact resolve eq28 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18213 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq18211
  have eq18214 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq18213
  have eq19212 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18214 eq104
    | exact resolve eq104 eq18214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq19213 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18214 eq108
    | exact resolve eq108 eq18214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18214
  have eq19234 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq19213
  have eq19248 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19234
       have r₂ := eq18212
       grind)
    | exact resolve eq19234 eq18212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19234
  have eq19249 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq19212
    | exact resolve eq19212 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19212
  have eq19267 : (k (M.op y y) y) = (τ (k (σ y) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19248 eq526
    | exact resolve eq526 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq19285 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq19248 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq19248
       grind)
    | exact resolve eq14 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19248
  have eq19310 : (τ (M.op (σ y) (σ y))) = (k (M.op y y) y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19267
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq19267
    | exact resolve eq19267 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19267
  have eq19318 : (M.op y y) = (k (M.op y y) y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq119 eq19310
    | exact resolve eq19310 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19310
  have eq19325 : (τ (σ y)) = (M.op y y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19249 eq119
    | exact resolve eq119 eq19249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19378 : y = (k y x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq19325
    | exact resolve eq19325 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19325
  have eq24048 : (σ (M.op y y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq19318
       grind)
    | exact superpose eq19318 eq185
    | exact resolve eq185 eq19318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq19318
  have eq24060 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24048
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq24048
    | exact resolve eq24048 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24048
  have eq27183 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19249 eq24060
    | exact resolve eq24060 eq19249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24060
  have eq27211 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq27183
  have eq27215 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq27211
       have r₂ := eq66
       grind)
    | exact resolve eq27211 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27211
  have eq27216 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq27215
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq27215
    | exact resolve eq27215 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq27215
  have eq27473 : (τ (σ y)) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq27216 eq119
    | exact resolve eq119 eq27216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq27216
  have eq27544 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq27473
    | exact resolve eq27473 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27473
  have eq27950 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq27544
  have eq27963 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq27950
       have r₂ := eq19378
       grind)
    | exact resolve eq27950 eq19378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19378 eq27950
  have eq27994 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq27963
       grind)
    | exact superpose eq27963 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq27963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq27963
  have eq27997 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq27994
  have eq28005 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27997
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq27997
    | exact resolve eq27997 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27997
  have eq28019 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28005
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28005
    | exact resolve eq28005 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28005
  have eq28024 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28019
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28019
    | exact resolve eq28019 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28019
  have eq28026 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq28024
    | exact resolve eq28024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28024
  have eq28028 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28026
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28026
    | exact resolve eq28026 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28026
  have eq28030 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28028
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28028
    | exact resolve eq28028 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28028
  have eq28031 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq28030
  have eq28033 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28031
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28031
    | exact resolve eq28031 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28031
  have eq28035 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28033
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28033
    | exact resolve eq28033 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28033
  have eq28038 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq28035
    | exact resolve eq28035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28035
  have eq48107 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19285
    | (have j0 := eq19285 (σ x)
       grind)
    | exact resolve eq19285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19285
  have eq48132 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48107
       have r₂ := eq17248
       grind)
    | exact resolve eq48107 eq17248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17248 eq48107
  have eq48145 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48132 eq108
    | exact resolve eq108 eq48132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq48132
  have eq48188 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq48145
  have eq48202 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48188
       have r₂ := eq18212
       grind)
    | exact resolve eq48188 eq18212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48188
  have eq48213 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq48202
       grind)
    | exact superpose eq48202 eq97
    | exact resolve eq97 eq48202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48238 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq48202
       grind)
    | exact superpose eq48202 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq48202
       grind)
    | exact resolve eq14 eq48202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48202
  have eq48271 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq48213
    | exact resolve eq48213 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48213
  have eq48556 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48271 eq19249
    | exact resolve eq19249 eq48271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19249 eq48271
  have eq48612 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq48556
  have eq48634 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq48612
       have r₂ := eq18212
       grind)
    | exact resolve eq48612 eq18212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18212 eq48612
  have eq51959 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48238 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48238
    | (have j0 := eq48238 x
       grind)
    | (have r₁ := eq48238 x
       have r₂ := eq19
       grind)
    | exact resolve eq48238 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48238
  have eq51982 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51959
  have eq52031 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48634
       have i₂ := eq51982
       grind)
    | exact superpose eq51982 eq48634
    | exact resolve eq48634 eq51982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48634 eq51982
  have eq52048 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq52031
  have eq52119 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq52048 eq30
    | exact resolve eq30 eq52048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq52048
  have eq52243 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq52119
    | exact resolve eq52119 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52119
  have eq52244 : y = (M.op x y) ∨ x = y := by grind
  clear eq52243
  have eq52263 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq52244 eq21
    | exact resolve eq21 eq52244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52266 : y ≠ y ∨ x = y ∨ y = (M.op y y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq52244 eq66
    | (have r₁ := eq66
       have r₂ := eq52244
       grind)
    | exact resolve eq66 eq52244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq52271 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq52244 eq120
    | exact resolve eq120 eq52244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq52392 : y ≠ y ∨ x = y ∨ y = (M.op y y) ∨ y = (k y x) := by grind
  clear eq52266
  have eq52393 : y = (k y x) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq52392
  have eq52502 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52271 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq52271
    | exact resolve eq52271 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq52271
  have eq52509 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52263
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52263
    | exact resolve eq52263 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52263
  have eq52535 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52509 eq27
    | exact resolve eq27 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52600 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq52509 eq5487
    | exact resolve eq5487 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5487
  have eq52674 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq52509 eq28038
    | exact resolve eq28038 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28038
  have eq52757 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq52674
  have eq52840 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq52757
       have r₂ := eq28
       grind)
    | exact resolve eq52757 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52757
  have eq52850 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq52600
       have r₂ := eq28
       grind)
    | exact resolve eq52600 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52600
  have eq52934 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52535 eq14
    | (have j0 := eq14 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq14 eq52535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52535
  have eq80578 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq52393
       grind)
    | exact superpose eq52393 eq90
    | exact resolve eq90 eq52393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52393
  have eq80642 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq80578
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80578
    | exact resolve eq80578 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80578
  have eq80665 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq52509 eq80642
    | exact resolve eq80642 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80642
  have eq80743 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq80665
  have eq410636 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq52840 eq52934
    | (have r₁ := eq52934
       have r₂ := eq52840
       grind)
    | exact resolve eq52934 eq52840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52840 eq52934
  have eq410664 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq410636
  have eq410665 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq410664
  have eq879055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq410665 eq80743
    | exact resolve eq80743 eq410665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80743 eq410665
  have eq879096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq879055
  have eq879108 : y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq879096
       have r₂ := eq28
       grind)
    | exact resolve eq879096 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879096
  have eq879120 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq879108
       grind)
    | exact superpose eq879108 eq97
    | exact resolve eq97 eq879108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq879185 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq879108
       grind)
    | exact superpose eq879108 eq14
    | exact resolve eq14 eq879108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879108
  have eq879265 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq879120
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq879120
    | exact resolve eq879120 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879120
  have eq879271 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq52509 eq879265
    | exact resolve eq879265 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879265
  have eq879499 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq879271
  have eq3320049 : y ≠ (M.op x y) ∨ y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq879185 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq879185
    | (have j0 := eq879185 x
       grind)
    | exact resolve eq879185 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879185
  have eq3320085 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3320049
       have r₂ := eq52244
       grind)
    | exact resolve eq3320049 eq52244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320049
  have eq3320098 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq3320085
       grind)
    | exact superpose eq3320085 eq90
    | exact resolve eq90 eq3320085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3320085
  have eq3320784 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3320098
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3320098
    | exact resolve eq3320098 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320098
  have eq3321031 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3320784 eq52502
    | exact resolve eq52502 eq3320784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52502 eq3320784
  have eq3321152 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3321031
  have eq3321376 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3321152 eq52850
    | exact resolve eq52850 eq3321152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52850 eq3321152
  have eq3321433 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq3321376
  have eq3321456 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3321433
       have r₂ := eq52509
       grind)
    | exact resolve eq3321433 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52509 eq3321433
  have eq3322753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq3321456 eq879499
    | exact resolve eq879499 eq3321456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879499 eq3321456
  have eq3322806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3322753
  have eq3322852 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3322806
       have r₂ := eq28
       grind)
    | exact resolve eq3322806 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322806
  have eq3322856 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3322852 eq29
    | exact resolve eq29 eq3322852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3322852
  have eq3323883 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq3322856
    | exact resolve eq3322856 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3322856
  have eq3325475 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3323883 eq52244
    | exact resolve eq52244 eq3323883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52244 eq3323883
  have eq3327960 : x = y := by grind
  clear eq3325475
  have eq3330057 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3327960
       grind)
    | exact superpose eq3327960 eq19
    | exact resolve eq19 eq3327960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3330058 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3327960
       grind)
    | exact superpose eq3327960 eq25
    | exact resolve eq25 eq3327960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3327960
  have eq3332948 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3330058
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3330058
    | exact resolve eq3330058 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3330058
  have eq3333516 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3332948 eq27
    | exact resolve eq27 eq3332948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3332948
  have eq3336708 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3333516 eq69
    | exact resolve eq69 eq3333516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3333516
  have eq3336800 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3336708
       have i₂ := eq3330057
       grind)
    | exact superpose eq3330057 eq3336708
    | exact resolve eq3336708 eq3330057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330057 eq3336708
  have eq3336871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3336800 eq15
    | exact resolve eq15 eq3336800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336800
  have eq3337766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq3336871
    | exact resolve eq3336871 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3336871
  have eq3338008 : False := by grind
  exact eq3338008

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then Y else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_x_y_pyx_x_pxx_y_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq10
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq66 : y ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ y = (k y x) := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq51 sF2
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq68
    | exact resolve eq68 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq91
    | exact resolve eq91 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq51 y
       grind)
    | exact superpose eq51 eq95
    | exact resolve eq95 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq119 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq185 : (σ (k (M.op y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq41
    | exact resolve eq41 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq318 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq474 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq318 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq318
    | (have j0 := eq318 X0 y
       grind)
    | exact resolve eq318 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq526 : (k (M.op y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq119 eq474
    | exact resolve eq474 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq566 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq75
  have eq690 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq566 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq566 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq4828 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4859 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4828
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4828
    | exact resolve eq4828 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828
  have eq4950 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4859
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq4859
    | exact resolve eq4859 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq5034 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4950
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4950
    | exact resolve eq4950 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950
  have eq5118 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5034
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5034
    | exact resolve eq5034 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034
  have eq5201 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq5118
    | exact resolve eq5118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5118
  have eq5284 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5201
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5201
    | exact resolve eq5201 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5201
  have eq5366 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5284
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5284
    | exact resolve eq5284 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5284
  have eq5447 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5366
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5366
    | exact resolve eq5366 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5366
  have eq5479 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5447
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5447
    | exact resolve eq5447 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447
  have eq5487 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq5479
    | exact resolve eq5479 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5479
  have eq16643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16643
    | exact resolve eq16643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16643
  have eq16655 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq16644
       have r₂ := eq28
       grind)
    | exact resolve eq16644 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16644
  have eq16659 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16655
    | exact resolve eq16655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16655
  have eq16661 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16659
    | exact resolve eq16659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16659
  have eq16672 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16661 eq14
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq16661
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq16661
       grind)
    | exact resolve eq14 eq16661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16661
  have eq17222 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq16672
    | (have j0 := eq16672 (σ x)
       grind)
    | (have r₁ := eq16672 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq16672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16672
  have eq17226 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq17222
  have eq17234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq17226 eq108
    | exact resolve eq108 eq17226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17226
  have eq17245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17234
  have eq17248 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17245
       have r₂ := eq28
       grind)
    | exact resolve eq17245 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17245
  have eq17323 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq17248
       grind)
    | exact superpose eq17248 eq97
    | exact resolve eq97 eq17248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17333 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq17248
       grind)
    | exact superpose eq17248 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq17248
       grind)
    | exact resolve eq14 eq17248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17347 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17323
    | exact resolve eq17323 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323
  have eq18064 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17333 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17333
    | (have j0 := eq17333 x
       grind)
    | (have r₁ := eq17333 x
       have r₂ := eq19
       grind)
    | exact resolve eq17333 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17333
  have eq18070 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18064
  have eq18085 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq690 x y
       have i₂ := eq18070
       grind)
    | exact superpose eq18070 eq690
    | (have j0 := eq690 x y
       grind)
    | exact resolve eq690 eq18070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq18070
  have eq18091 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18085
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18085
    | exact resolve eq18085 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18085
  have eq18103 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq18091
    | exact resolve eq18091 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18091
  have eq18107 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18103
       have r₂ := eq17347
       grind)
    | exact resolve eq18103 eq17347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18103
  have eq18109 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18107
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq18107
    | exact resolve eq18107 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18107
  have eq18111 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18109
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18109
    | exact resolve eq18109 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18109
  have eq18113 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18111
    | exact resolve eq18111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18111
  have eq18115 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq18113
    | exact resolve eq18113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18113
  have eq18118 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18115
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18115
    | exact resolve eq18115 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18115
  have eq18120 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18118
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18118
    | exact resolve eq18118 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18121 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18120
  have eq18123 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18121
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18121
    | exact resolve eq18121 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18121
  have eq18126 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18123
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18123
    | exact resolve eq18123 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq18127 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18126
    | exact resolve eq18126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18126
  have eq18128 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq18127
  have eq18191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18128 eq17347
    | exact resolve eq17347 eq18128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17347 eq18128
  have eq18202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq18191
  have eq18209 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18202
       have r₂ := eq28
       grind)
    | exact resolve eq18202 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18202
  have eq18211 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18209 eq67
    | (have r₁ := eq67
       have r₂ := eq18209
       grind)
    | exact resolve eq67 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq18212 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18209 eq28
    | exact resolve eq28 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18213 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq18211
  have eq18214 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq18213
  have eq19212 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18214 eq104
    | exact resolve eq104 eq18214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq19213 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18214 eq108
    | exact resolve eq108 eq18214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18214
  have eq19234 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq19213
  have eq19248 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19234
       have r₂ := eq18212
       grind)
    | exact resolve eq19234 eq18212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19234
  have eq19249 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq19212
    | exact resolve eq19212 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19212
  have eq19267 : (k (M.op y y) y) = (τ (k (σ y) (σ y))) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19248 eq526
    | exact resolve eq526 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq19285 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq19248 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq19248
       grind)
    | exact resolve eq14 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19248
  have eq19310 : (τ (M.op (σ y) (σ y))) = (k (M.op y y) y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19267
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq19267
    | exact resolve eq19267 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19267
  have eq19318 : (M.op y y) = (k (M.op y y) y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq119 eq19310
    | exact resolve eq19310 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19310
  have eq19325 : (τ (σ y)) = (M.op y y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19249 eq119
    | exact resolve eq119 eq19249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19378 : y = (k y x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq19325
    | exact resolve eq19325 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19325
  have eq24048 : (σ (M.op y y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq19318
       grind)
    | exact superpose eq19318 eq185
    | exact resolve eq185 eq19318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq19318
  have eq24060 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24048
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq24048
    | exact resolve eq24048 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24048
  have eq27183 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19249 eq24060
    | exact resolve eq24060 eq19249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24060
  have eq27211 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq27183
  have eq27215 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq27211
       have r₂ := eq66
       grind)
    | exact resolve eq27211 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27211
  have eq27216 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq27215
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq27215
    | exact resolve eq27215 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq27215
  have eq27473 : (τ (σ y)) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq27216 eq119
    | exact resolve eq119 eq27216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq27216
  have eq27544 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq27473
    | exact resolve eq27473 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27473
  have eq27950 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq27544
  have eq27963 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq27950
       have r₂ := eq19378
       grind)
    | exact resolve eq27950 eq19378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19378 eq27950
  have eq27994 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq691 x y
       have i₂ := eq27963
       grind)
    | exact superpose eq27963 eq691
    | (have j0 := eq691 x y
       grind)
    | exact resolve eq691 eq27963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq27963
  have eq27997 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq27994
  have eq28005 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27997
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq27997
    | exact resolve eq27997 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27997
  have eq28019 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28005
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28005
    | exact resolve eq28005 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28005
  have eq28024 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28019
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28019
    | exact resolve eq28019 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28019
  have eq28026 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq28024
    | exact resolve eq28024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28024
  have eq28028 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28026
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28026
    | exact resolve eq28026 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28026
  have eq28030 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28028
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28028
    | exact resolve eq28028 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28028
  have eq28031 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq28030
  have eq28033 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28031
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28031
    | exact resolve eq28031 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28031
  have eq28035 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq28033
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28033
    | exact resolve eq28033 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28033
  have eq28038 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq28035
    | exact resolve eq28035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28035
  have eq48107 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq19285
    | (have j0 := eq19285 (σ x)
       grind)
    | exact resolve eq19285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19285
  have eq48132 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48107
       have r₂ := eq17248
       grind)
    | exact resolve eq48107 eq17248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17248 eq48107
  have eq48145 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48132 eq108
    | exact resolve eq108 eq48132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq48132
  have eq48188 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq48145
  have eq48202 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq48188
       have r₂ := eq18212
       grind)
    | exact resolve eq48188 eq18212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48188
  have eq48213 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq48202
       grind)
    | exact superpose eq48202 eq97
    | exact resolve eq97 eq48202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48238 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq48202
       grind)
    | exact superpose eq48202 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq48202
       grind)
    | exact resolve eq14 eq48202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48202
  have eq48271 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq48213
    | exact resolve eq48213 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48213
  have eq48556 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq48271 eq19249
    | exact resolve eq19249 eq48271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19249 eq48271
  have eq48612 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq48556
  have eq48634 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq48612
       have r₂ := eq18212
       grind)
    | exact resolve eq48612 eq18212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18212 eq48612
  have eq51959 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48238 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48238
    | (have j0 := eq48238 x
       grind)
    | (have r₁ := eq48238 x
       have r₂ := eq19
       grind)
    | exact resolve eq48238 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48238
  have eq51982 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51959
  have eq52031 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48634
       have i₂ := eq51982
       grind)
    | exact superpose eq51982 eq48634
    | exact resolve eq48634 eq51982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48634 eq51982
  have eq52048 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq52031
  have eq52119 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq52048 eq30
    | exact resolve eq30 eq52048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq52048
  have eq52243 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq52119
    | exact resolve eq52119 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52119
  have eq52244 : y = (M.op x y) ∨ x = y := by grind
  clear eq52243
  have eq52263 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq52244 eq21
    | exact resolve eq21 eq52244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52266 : y ≠ y ∨ x = y ∨ y = (M.op y y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq52244 eq66
    | (have r₁ := eq66
       have r₂ := eq52244
       grind)
    | exact resolve eq66 eq52244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq52271 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq52244 eq120
    | exact resolve eq120 eq52244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq52392 : y ≠ y ∨ x = y ∨ y = (M.op y y) ∨ y = (k y x) := by grind
  clear eq52266
  have eq52393 : y = (k y x) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq52392
  have eq52502 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52271 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq52271
    | exact resolve eq52271 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq52271
  have eq52509 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52263
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52263
    | exact resolve eq52263 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52263
  have eq52535 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52509 eq27
    | exact resolve eq27 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52600 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq52509 eq5487
    | exact resolve eq5487 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5487
  have eq52674 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq52509 eq28038
    | exact resolve eq28038 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28038
  have eq52757 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq52674
  have eq52840 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq52757
       have r₂ := eq28
       grind)
    | exact resolve eq52757 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52757
  have eq52850 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq52600
       have r₂ := eq28
       grind)
    | exact resolve eq52600 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52600
  have eq52934 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52535 eq14
    | (have j0 := eq14 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq14 eq52535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52535
  have eq80578 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq52393
       grind)
    | exact superpose eq52393 eq90
    | exact resolve eq90 eq52393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52393
  have eq80642 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq80578
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80578
    | exact resolve eq80578 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80578
  have eq80665 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq52509 eq80642
    | exact resolve eq80642 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80642
  have eq80743 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq80665
  have eq410636 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq52840 eq52934
    | (have r₁ := eq52934
       have r₂ := eq52840
       grind)
    | exact resolve eq52934 eq52840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52840 eq52934
  have eq410664 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq410636
  have eq410665 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by grind
  clear eq410664
  have eq879055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq410665 eq80743
    | exact resolve eq80743 eq410665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80743 eq410665
  have eq879096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq879055
  have eq879108 : y = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq879096
       have r₂ := eq28
       grind)
    | exact resolve eq879096 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879096
  have eq879120 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq879108
       grind)
    | exact superpose eq879108 eq97
    | exact resolve eq97 eq879108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq879185 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y x
       have i₂ := eq879108
       grind)
    | exact superpose eq879108 eq14
    | exact resolve eq14 eq879108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879108
  have eq879265 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq879120
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq879120
    | exact resolve eq879120 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879120
  have eq879271 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq52509 eq879265
    | exact resolve eq879265 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879265
  have eq879499 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq879271
  have eq3320049 : y ≠ (M.op x y) ∨ y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq879185 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq879185
    | (have j0 := eq879185 x
       grind)
    | exact resolve eq879185 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879185
  have eq3320085 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3320049
       have r₂ := eq52244
       grind)
    | exact resolve eq3320049 eq52244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320049
  have eq3320098 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq3320085
       grind)
    | exact superpose eq3320085 eq90
    | exact resolve eq90 eq3320085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3320085
  have eq3320784 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3320098
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3320098
    | exact resolve eq3320098 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320098
  have eq3321031 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3320784 eq52502
    | exact resolve eq52502 eq3320784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52502 eq3320784
  have eq3321152 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3321031
  have eq3321376 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3321152 eq52850
    | exact resolve eq52850 eq3321152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52850 eq3321152
  have eq3321433 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq3321376
  have eq3321456 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3321433
       have r₂ := eq52509
       grind)
    | exact resolve eq3321433 eq52509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52509 eq3321433
  have eq3322753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq3321456 eq879499
    | exact resolve eq879499 eq3321456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879499 eq3321456
  have eq3322806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3322753
  have eq3322852 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3322806
       have r₂ := eq28
       grind)
    | exact resolve eq3322806 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322806
  have eq3322856 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3322852 eq29
    | exact resolve eq29 eq3322852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3322852
  have eq3323883 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq3322856
    | exact resolve eq3322856 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3322856
  have eq3325475 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3323883 eq52244
    | exact resolve eq52244 eq3323883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52244 eq3323883
  have eq3327960 : x = y := by grind
  clear eq3325475
  have eq3330057 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3327960
       grind)
    | exact superpose eq3327960 eq19
    | exact resolve eq19 eq3327960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3330058 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3327960
       grind)
    | exact superpose eq3327960 eq25
    | exact resolve eq25 eq3327960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3327960
  have eq3332948 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3330058
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3330058
    | exact resolve eq3330058 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3330058
  have eq3333516 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3332948 eq27
    | exact resolve eq27 eq3332948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3332948
  have eq3336708 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3333516 eq69
    | exact resolve eq69 eq3333516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3333516
  have eq3336800 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3336708
       have i₂ := eq3330057
       grind)
    | exact superpose eq3330057 eq3336708
    | exact resolve eq3336708 eq3330057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330057 eq3336708
  have eq3336871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3336800 eq15
    | exact resolve eq15 eq3336800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336800
  have eq3337766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq3336871
    | exact resolve eq3336871 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3336871
  have eq3338008 : False := by grind
  exact eq3338008

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then X else if m(X,Y) = X then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pxx_pxy_pxy_x_pxy_x_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
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
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq16
    | exact resolve eq16 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq19
    | exact resolve eq19 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq30 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq21
    | exact resolve eq21 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq66 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq30
    | exact resolve eq30 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq129 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq66
    | exact resolve eq66 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) ≠ (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq176
    | (have j0 := eq176 X0 X1
       grind)
    | (have r₁ := eq176 X0 X0
       have r₂ := eq174 X0
       grind)
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq223 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq129
    | exact resolve eq129 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq129 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq129
    | exact resolve eq129 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq467 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq223
    | exact resolve eq223 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq510 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq231 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq231
    | exact resolve eq231 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq788 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq467 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq467
    | exact resolve eq467 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq842 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq510 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq510
    | exact resolve eq510 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq1203 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq17 x y
       grind)
    | exact superpose eq17 eq9
    | (have j1 := eq17 x y
       grind)
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq17 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1206 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq17 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1206 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq1206
    | (have j0 := eq1206 X0 X1
       grind)
    | (have r₁ := eq1206 X0 X0
       have r₂ := eq174 X0
       grind)
    | exact resolve eq1206 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1208 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1205 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq1205
    | (have j0 := eq1205 X0 X1
       grind)
    | exact resolve eq1205 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1210 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1203
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1203
    | exact resolve eq1203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1211 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1207 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq1207
    | (have j0 := eq1207 X0 X1
       grind)
    | exact resolve eq1207 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1213 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1210
    | exact resolve eq1210 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1291 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1213
       have i₂ := eq17 (σ x) (σ y)
       grind)
    | exact superpose eq17 eq1213
    | (have j1 := eq17 (σ x) (σ y)
       grind)
    | (have r₁ := eq1213
       have r₂ := eq17 (σ x) (σ y)
       grind)
    | exact resolve eq1213 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1292 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1291
  have eq1293 : x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1292
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq1292
    | exact resolve eq1292 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1372 : x ≠ (k x x) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq1788 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq788 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq788
    | exact resolve eq788 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq2057 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq842 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq842
    | exact resolve eq842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2223 : x ≠ x ∨ x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1293
       grind)
    | exact superpose eq1293 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1293
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1293
       grind)
    | exact resolve eq12 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq2224 : x = (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2223
  have eq2226 : x = (k x x) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2224
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq2224
    | exact resolve eq2224 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2228 : (M.op x x) = (k y y) ∨ x = (k x x) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2226
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq2226
    | exact resolve eq2226 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq2230 : (k x x) = (k y y) ∨ x = (k x x) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2228
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq2228
    | exact resolve eq2228 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq2232 : (k x y) = (k x x) ∨ (k x x) = (k y y) ∨ x = (k x x) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq2230
    | exact resolve eq2230 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2234 : (k x y) = (k x x) ∨ (k x x) = (k y y) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2232
       have r₂ := eq1372
       grind)
    | exact resolve eq2232 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq2306 : (k (σ x) (σ y)) = (σ (k x x)) ∨ (k x x) = (k y y) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq2234
       grind)
    | exact superpose eq2234 eq10
    | exact resolve eq10 eq2234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234
  have eq2307 : (k x x) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2306
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2306
    | exact resolve eq2306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq2380 : (σ (k x x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2307
       grind)
    | exact superpose eq2307 eq10
    | exact resolve eq10 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2381 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2380
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2380
    | exact resolve eq2380 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2457 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2381
       grind)
    | exact superpose eq2381 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq2381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381
  have eq2462 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2457
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq2457
    | (have r₁ := eq2457
       have r₂ := eq174 (σ x)
       grind)
    | exact resolve eq2457 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2463 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2462
  have eq2465 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2463
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq2463
    | exact resolve eq2463 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq2466 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2465
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq2465
    | exact resolve eq2465 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465
  have eq2467 : (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2466
  have eq2539 : x ≠ (k x y) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1208 x y
       grind)
    | exact superpose eq1208 eq9
    | (have j1 := eq1208 x y
       grind)
    | exact resolve eq9 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2544 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq1208 X0 X1
       grind)
    | exact superpose eq1208 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq1208 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1208 X0 X1
       grind)
    | exact resolve eq12 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2547 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1208 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2549 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544
  have eq2550 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2549 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq2549
    | (have j0 := eq2549 X0 X1
       grind)
    | exact resolve eq2549 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549
  have eq2554 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2550 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq2550
    | (have j0 := eq2550 X0 X1
       grind)
    | exact resolve eq2550 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq2555 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2554 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq2554
    | (have j0 := eq2554 X0 X1
       grind)
    | exact resolve eq2554 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq2556 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X0 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2555 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq2555
    | (have j0 := eq2555 X0 X1
       grind)
    | exact resolve eq2555 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2557 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X0) = (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2556 X0 X1
       have j1 := eq2547 X0 X1
       grind)
    | (have r₁ := eq2556 (k X1 X1) X1
       have r₂ := eq2547 (k X1 X1) X1
       grind)
    | (have r₁ := eq2556 X0 (k X0 X0)
       have r₂ := eq2547 (k X0 X0) X1
       grind)
    | (have r₁ := eq2556 (k X1 X1) X1
       have r₂ := eq2547 (k X1 X1) (k X1 X1)
       grind)
    | exact resolve eq2556 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547 eq2556
  have eq2776 : (M.op x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2467
       grind)
    | exact superpose eq2467 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467
  have eq2778 : (k x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2776
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq2776
    | (have r₁ := eq2776
       have r₂ := eq174 x
       grind)
    | exact resolve eq2776 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2776
  have eq2779 : (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2778
  have eq2782 : (M.op x x) = (k y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2779
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq2779
    | exact resolve eq2779 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq2783 : (k x x) = (k y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2782
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq2782
    | exact resolve eq2782 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782
  have eq2855 : (σ (k x x)) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2783
       grind)
    | exact superpose eq2783 eq10
    | exact resolve eq10 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq2856 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2855
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2855
    | exact resolve eq2855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2855
  have eq2857 : x = (k x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2856
  have eq2934 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq2857
       grind)
    | exact superpose eq2857 eq10
    | exact resolve eq10 eq2857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq2935 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq2934
  have eq3012 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq2935
       grind)
    | exact superpose eq2935 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2935
       grind)
    | exact resolve eq12 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935
  have eq3015 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq3012
  have eq3019 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3015
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq3015
    | exact resolve eq3015 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015
  have eq3022 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3019
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq3019
    | exact resolve eq3019 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019
  have eq3025 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3022
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq3022
    | exact resolve eq3022 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq3026 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq3025
  have eq3027 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3026
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq3026
    | exact resolve eq3026 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3028 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq3027
  have eq3195 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (k (τ X0) (τ X0)) = (k (τ X1) (τ X1)) ∨ (τ (k X0 X1)) = (k (τ X0) (τ X0)) ∨ (k (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2557 (τ X0) (τ X1)
       have i₂ := eq1788 X0 X1
       grind)
    | exact superpose eq1788 eq2557
    | (have j0 := eq2557 (τ X0) (τ X1)
       grind)
    | exact resolve eq2557 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788
  have eq3198 : ∀ X0 X1 : G, (k (τ X0) (τ X0)) = (τ (k X1 X1)) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (k (τ X0) (τ X0)) ∨ (k (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3195 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq3195
    | (have j0 := eq3195 X0 X1
       grind)
    | exact resolve eq3195 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195
  have eq3225 : ∀ X0 X1 : G, (τ (k X1 X1)) = (τ (k X0 X0)) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (k (τ X0) (τ X0)) ∨ (k (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3198 X0 X1
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq3198
    | (have j0 := eq3198 X0 X1
       grind)
    | exact resolve eq3198 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3198
  have eq3252 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k X0 X0)) ∨ (τ (k X1 X1)) = (τ (k X0 X0)) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (k (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3225 X0 X1
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq3225
    | (have j0 := eq3225 X0 X1
       grind)
    | exact resolve eq3225 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq3279 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (k X0 X0)) ∨ (τ (k X1 X1)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X1)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3252 X0 X1
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq3252
    | (have j0 := eq3252 X0 X1
       grind)
    | exact resolve eq3252 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3252
  have eq3308 : (k x y) ≠ (k x x) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1211 x y
       grind)
    | exact superpose eq1211 eq9
    | (have j1 := eq1211 x y
       grind)
    | exact resolve eq9 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3410 : (k y y) = (τ (k (σ x) (σ x))) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq3028
       grind)
    | exact superpose eq3028 eq18
    | exact resolve eq18 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3475 : (k x x) = (k y y) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3410
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq3410
    | exact resolve eq3410 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410
  have eq3617 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2057 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2057
    | exact resolve eq2057 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq6566 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq177 x y
       grind)
    | exact superpose eq177 eq9
    | (have j1 := eq177 x y
       grind)
    | exact resolve eq9 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6591 : (k x x) ≠ (k y y) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6566
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq6566
    | exact resolve eq6566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6566
  have eq6599 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6591
       have i₂ := eq3475
       grind)
    | exact superpose eq3475 eq6591
    | (have r₁ := eq6591
       have r₂ := eq3475
       grind)
    | exact resolve eq6591 eq3475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475
  have eq6601 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6591
       have i₂ := eq2307
       grind)
    | exact superpose eq2307 eq6591
    | (have r₁ := eq6591
       have r₂ := eq2307
       grind)
    | exact resolve eq6591 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq6602 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6601
  have eq6604 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq6599
  have eq7159 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq6604
       have i₂ := eq177 (σ x) (σ y)
       grind)
    | exact superpose eq177 eq6604
    | (have j1 := eq177 (σ x) (σ y)
       grind)
    | (have r₁ := eq6604
       have r₂ := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq6604 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6604
  have eq7165 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq7159
  have eq7169 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq7165
       have r₂ := eq3028
       grind)
    | exact resolve eq7165 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028 eq7165
  have eq7355 : (k x y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18 x y
       have i₂ := eq7169
       grind)
    | exact superpose eq7169 eq18
    | exact resolve eq18 eq7169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7449 : (k x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7355
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq7355
    | exact resolve eq7355 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7355
  have eq7685 : (k x x) ≠ (k x x) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3308
       have i₂ := eq7449
       grind)
    | exact superpose eq7449 eq3308
    | (have r₁ := eq3308
       have r₂ := eq7449
       grind)
    | exact resolve eq3308 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq7691 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq7685
  have eq8231 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq7691
       have i₂ := eq1211 (σ x) (σ y)
       grind)
    | exact superpose eq1211 eq7691
    | (have j1 := eq1211 (σ x) (σ y)
       grind)
    | (have r₁ := eq7691
       have r₂ := eq1211 (σ x) (σ y)
       grind)
    | exact resolve eq7691 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq8234 : (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq8231
  have eq8238 : (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq8234
       have r₂ := eq7169
       grind)
    | exact resolve eq8234 eq7169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7169 eq8234
  have eq9833 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6602
       have i₂ := eq17 (σ x) (σ y)
       grind)
    | exact superpose eq17 eq6602
    | (have j1 := eq17 (σ x) (σ y)
       grind)
    | (have r₁ := eq6602
       have r₂ := eq17 (σ x) (σ y)
       grind)
    | exact resolve eq6602 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq6602
  have eq9834 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq9833
  have eq9835 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq9834
  have eq9838 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9835
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq9835
    | exact resolve eq9835 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9835
  have eq9840 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8238 eq9838
    | exact resolve eq9838 eq8238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8238 eq9838
  have eq9841 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9840
  have eq10239 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq9841
       grind)
    | exact superpose eq9841 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq9841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9841
  have eq10241 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10239
  have eq10248 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10241
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq10241
    | (have r₁ := eq10241
       have r₂ := eq174 (σ x)
       grind)
    | exact resolve eq10241 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10241
  have eq10249 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10248
  have eq10254 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10249
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq10249
    | exact resolve eq10249 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10249
  have eq10257 : (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10254
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq10254
    | exact resolve eq10254 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10254
  have eq11684 : (M.op x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq10257
       grind)
    | exact superpose eq10257 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq10257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10257
  have eq11688 : (k x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11684
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq11684
    | (have r₁ := eq11684
       have r₂ := eq174 x
       grind)
    | exact resolve eq11684 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11684
  have eq11689 : (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11688
  have eq11694 : (M.op x x) = (k y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11689
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq11689
    | exact resolve eq11689 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11689
  have eq11696 : (k x x) = (k y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11694
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq11694
    | exact resolve eq11694 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11694
  have eq13392 : (σ (k x x)) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq11696
       grind)
    | exact superpose eq11696 eq10
    | exact resolve eq10 eq11696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11696
  have eq13400 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13392
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq13392
    | exact resolve eq13392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13392
  have eq13401 : x = (k x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13400
  have eq13578 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq13401
       grind)
    | exact superpose eq13401 eq10
    | exact resolve eq10 eq13401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13401
  have eq13579 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq13578
  have eq13753 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7691
       have i₂ := eq13579
       grind)
    | exact superpose eq13579 eq7691
    | (have r₁ := eq7691
       have r₂ := eq13579
       grind)
    | exact resolve eq7691 eq13579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7691
  have eq13756 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq13579
       grind)
    | exact superpose eq13579 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq13579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13579
  have eq13757 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq13756
  have eq13760 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq13753
  have eq13761 : (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq13760
  have eq13767 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13757
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq13757
    | exact resolve eq13757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13757
  have eq13770 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13767
       have i₂ := eq174 (σ y)
       grind)
    | exact superpose eq174 eq13767
    | exact resolve eq13767 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13767
  have eq13772 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13770
       have i₂ := eq174 (σ x)
       grind)
    | exact superpose eq174 eq13770
    | exact resolve eq13770 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13770
  have eq13773 : (σ x) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq13772
  have eq14096 : (M.op x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq13761
       grind)
    | exact superpose eq13761 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq13761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13761
  have eq14099 : (k x x) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14096
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq14096
    | (have r₁ := eq14096
       have r₂ := eq174 x
       grind)
    | exact resolve eq14096 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14096
  have eq14100 : (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq14099
  have eq14105 : (M.op x x) = (k y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14100
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq14100
    | exact resolve eq14100 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14100
  have eq14106 : (k x x) = (k y y) ∨ x = (k x y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14105
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq14105
    | exact resolve eq14105 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14105
  have eq14107 : (k x x) = (k y y) ∨ x = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq7449 eq14106
    | exact resolve eq14106 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449 eq14106
  have eq14108 : x = (k x x) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq14107
       have r₂ := eq13773
       grind)
    | exact resolve eq14107 eq13773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14107
  have eq14267 : (σ x) = (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq14108
       grind)
    | exact superpose eq14108 eq10
    | exact resolve eq10 eq14108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14108
  have eq14273 : (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq14267
       have r₂ := eq13773
       grind)
    | exact resolve eq14267 eq13773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14267
  have eq14437 : (σ (k x x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq14273
       grind)
    | exact superpose eq14273 eq10
    | exact resolve eq10 eq14273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14273
  have eq14444 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14437
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq14437
    | exact resolve eq14437 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14437
  have eq14445 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq14444
  have eq14522 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (k (σ x) (σ x))) = (τ (σ x)) ∨ (τ (k (σ y) (σ y))) = (τ (k (σ x) (σ x))) ∨ (τ (k (σ x) (σ x))) = (M.op (τ (σ x)) (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3279 (σ x) (σ y)
       have i₂ := eq14445
       grind)
    | exact superpose eq14445 eq3279
    | (have j0 := eq3279 (σ x) (σ y)
       grind)
    | exact resolve eq3279 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq14523 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2557 (σ x) (σ y)
       have i₂ := eq14445
       grind)
    | exact superpose eq14445 eq2557
    | (have j0 := eq2557 (σ x) (σ y)
       grind)
    | (have r₁ := eq2557 (σ x) (σ y)
       have r₂ := eq14445
       grind)
    | exact resolve eq2557 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557 eq14445
  have eq14526 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq14523
  have eq14527 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq14526
  have eq14528 : (τ (k (σ x) (σ x))) = (τ (σ x)) ∨ (τ (k (σ y) (σ y))) = (τ (k (σ x) (σ x))) ∨ (τ (k (σ x) (σ x))) = (M.op (τ (σ x)) (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq14522
  have eq14531 : x = (τ (k (σ x) (σ x))) ∨ (τ (k (σ y) (σ y))) = (τ (k (σ x) (σ x))) ∨ (τ (k (σ x) (σ x))) = (M.op (τ (σ x)) (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14528
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq14528
    | exact resolve eq14528 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14528
  have eq14597 : x = (k x x) ∨ (τ (k (σ y) (σ y))) = (τ (k (σ x) (σ x))) ∨ (τ (k (σ x) (σ x))) = (M.op (τ (σ x)) (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14531
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq14531
    | exact resolve eq14531 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14531
  have eq14629 : (k x x) = (τ (k (σ y) (σ y))) ∨ x = (k x x) ∨ (τ (k (σ x) (σ x))) = (M.op (τ (σ x)) (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14597
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq14597
    | exact resolve eq14597 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14597
  have eq14630 : (k x x) = (k y y) ∨ x = (k x x) ∨ (τ (k (σ x) (σ x))) = (M.op (τ (σ x)) (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14629
       have i₂ := eq18 y y
       grind)
    | exact superpose eq18 eq14629
    | exact resolve eq14629 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14629
  have eq14631 : (τ (k (σ x) (σ x))) = (M.op (τ (σ x)) y) ∨ (k x x) = (k y y) ∨ x = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14630
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq14630
    | exact resolve eq14630 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14630
  have eq14632 : (M.op x y) = (τ (k (σ x) (σ x))) ∨ (k x x) = (k y y) ∨ x = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14631
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq14631
    | exact resolve eq14631 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14631
  have eq14633 : x = (k x x) ∨ (k x x) = (k y y) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14632
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq14632
    | exact resolve eq14632 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14632
  have eq16623 : (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq14633
       grind)
    | exact superpose eq14633 eq10
    | exact resolve eq10 eq14633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14633
  have eq16789 : (σ (k x x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq16623
       grind)
    | exact superpose eq16623 eq10
    | exact resolve eq10 eq16623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16623
  have eq16794 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16789
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq16789
    | exact resolve eq16789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16789
  have eq16795 : (M.op x y) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq16794
  have eq16961 : (M.op (σ x) (σ y)) ≠ (σ (k x x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq16795
       grind)
    | exact superpose eq16795 eq9
    | exact resolve eq9 eq16795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16795
  have eq16970 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16961
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq16961
    | exact resolve eq16961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16961
  have eq16974 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq16970
       have r₂ := eq14527
       grind)
    | exact resolve eq16970 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14527 eq16970
  have eq16980 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq16974
       grind)
    | exact superpose eq16974 eq18
    | exact resolve eq18 eq16974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17111 : (k x x) = (k y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16980
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq16980
    | exact resolve eq16980 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16980
  have eq17177 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6591
       have i₂ := eq17111
       grind)
    | exact superpose eq17111 eq6591
    | (have r₁ := eq6591
       have r₂ := eq17111
       grind)
    | exact resolve eq6591 eq17111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6591 eq17111
  have eq17185 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq17177
  have eq17196 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq17185
       have i₂ := eq177 (σ x) (σ y)
       grind)
    | exact superpose eq177 eq17185
    | (have j1 := eq177 (σ x) (σ y)
       grind)
    | (have r₁ := eq17185
       have r₂ := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq17185 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17185
  have eq17202 : (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq17196
  have eq17205 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq17202
       have r₂ := eq16974
       grind)
    | exact resolve eq17202 eq16974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16974 eq17202
  have eq17207 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq13773
       have r₂ := eq17205
       grind)
    | exact resolve eq13773 eq17205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13773
  have eq17211 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq17207
       have i₂ := eq17205
       grind)
    | exact superpose eq17205 eq17207
    | exact resolve eq17207 eq17205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17207
  have eq17281 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | (have i₁ := eq3617 x (σ x)
       have i₂ := eq17205
       grind)
    | exact superpose eq17205 eq3617
    | exact resolve eq3617 eq17205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17286 : x = (k x x) := by
    first
    | (have i₁ := eq17281
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq17281
    | exact resolve eq17281 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17281
  have eq17353 : (M.op x y) = (k x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1372
       have r₂ := eq17286
       grind)
    | exact resolve eq1372 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq17356 : x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17353
       have i₂ := eq17286
       grind)
    | exact superpose eq17286 eq17353
    | exact resolve eq17353 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17353
  have eq17358 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17356
       have i₂ := eq17205
       grind)
    | exact superpose eq17205 eq17356
    | exact resolve eq17356 eq17205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17356
  have eq17359 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17358
  have eq17403 : x = (k x y) ∨ (k x x) ≠ (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17405 : x ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq17359
       grind)
    | exact superpose eq17359 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17411 : x ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17405
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq17405
    | exact resolve eq17405 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17405
  have eq17413 : x ≠ (k y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17403
       have i₂ := eq17286
       grind)
    | exact superpose eq17286 eq17403
    | exact resolve eq17403 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17403
  have eq17416 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17411
       have i₂ := eq17286
       grind)
    | exact superpose eq17286 eq17411
    | (have r₁ := eq17411
       have r₂ := eq17286
       grind)
    | exact resolve eq17411 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17411
  have eq17417 : (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17416
  have eq17420 : (M.op x x) = (k y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17417
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq17417
    | exact resolve eq17417 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17417
  have eq17421 : (k x x) = (k y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17420
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq17420
    | exact resolve eq17420 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq17420
  have eq17422 : x = (k y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17421
       have i₂ := eq17286
       grind)
    | exact superpose eq17286 eq17421
    | exact resolve eq17421 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17421
  have eq17423 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17422
       have r₂ := eq17413
       grind)
    | exact resolve eq17422 eq17413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17413 eq17422
  have eq17685 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq17423
       grind)
    | exact superpose eq17423 eq10
    | exact resolve eq10 eq17423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17423
  have eq18802 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq177 (σ x) (σ y)
       have i₂ := eq17685
       grind)
    | exact superpose eq17685 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq17685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq17685
  have eq18805 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq18802
  have eq18819 : (σ x) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq18805
       have i₂ := eq17205
       grind)
    | exact superpose eq17205 eq18805
    | exact resolve eq18805 eq17205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18805
  have eq18827 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq18819
       have r₂ := eq17211
       grind)
    | exact resolve eq18819 eq17211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17211 eq18819
  have eq20062 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq3617 y (σ x)
       have i₂ := eq18827
       grind)
    | exact superpose eq18827 eq3617
    | exact resolve eq3617 eq18827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617
  have eq20072 : x = (k x y) := by
    first
    | (have i₁ := eq20062
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq20062
    | exact resolve eq20062 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20062
  have eq20141 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq2539
       have r₂ := eq20072
       grind)
    | exact resolve eq2539 eq20072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2539 eq20072
  have eq20173 : x = (M.op x y) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20141
       have i₂ := eq17286
       grind)
    | exact superpose eq17286 eq20141
    | exact resolve eq20141 eq17286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17286 eq20141
  have eq20174 : x = (M.op x y) := by
    first
    | (have r₁ := eq20173
       have r₂ := eq17359
       grind)
    | exact resolve eq20173 eq17359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20173
  have eq20183 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20174
       grind)
    | exact superpose eq20174 eq9
    | exact resolve eq9 eq20174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20174
  have eq20231 : x = (M.op x y) := by
    first
    | (have r₁ := eq17359
       have r₂ := eq20183
       grind)
    | exact resolve eq17359 eq20183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17359
  have eq20287 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20231
       grind)
    | exact superpose eq20231 eq9
    | exact resolve eq9 eq20231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20231
  have eq20323 : (σ x) ≠ (σ x) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq20183
       have i₂ := eq1208 (σ x) (σ y)
       grind)
    | exact superpose eq1208 eq20183
    | (have j1 := eq1208 (σ x) (σ y)
       grind)
    | (have r₁ := eq20183
       have r₂ := eq1208 (σ x) (σ y)
       grind)
    | exact resolve eq20183 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq20183
  have eq20325 : (σ x) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq20323
  have eq20329 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq20325
       have i₂ := eq18827
       grind)
    | exact superpose eq18827 eq20325
    | (have r₁ := eq20325
       have r₂ := eq18827
       grind)
    | exact resolve eq20325 eq18827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18827 eq20325
  have eq20330 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq20329
  have eq20335 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20330
       have i₂ := eq17205
       grind)
    | exact superpose eq17205 eq20330
    | exact resolve eq20330 eq17205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17205 eq20330
  have eq20341 : False := by grind
  exact eq20341

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pxx_y_pyy_x_pxy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq44 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
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
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X1 X1)
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq46
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq46
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq46 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq82
    | exact resolve eq82 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq88
    | exact resolve eq88 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq52 sF3
       grind)
    | exact superpose eq52 eq97
    | exact resolve eq97 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq52 y
       grind)
    | exact superpose eq52 eq101
    | exact resolve eq101 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq121 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq16
    | exact resolve eq16 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq265 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
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
  have eq342 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq40
  have eq528 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq529 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq633 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq6121 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq265 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq265
    | (have j0 := eq265 X0
       grind)
    | exact resolve eq265 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq6122 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
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
  have eq6123 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6122 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq6122
    | (have j0 := eq6122 X0
       grind)
    | exact resolve eq6122 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6122
  have eq6124 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6123 X0
       have i₂ := eq633 (M.op X0 X0)
       grind)
    | exact superpose eq633 eq6123
    | (have j0 := eq6123 X0
       grind)
    | exact resolve eq6123 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6123
  have eq7800 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq342
    | (have j0 := eq342 X0
       grind)
    | exact resolve eq342 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq7801 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
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
  have eq7802 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7801 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq7801
    | (have j0 := eq7801 X0
       grind)
    | exact resolve eq7801 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq7803 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7802 X0
       have i₂ := eq633 (M.op X0 X0)
       grind)
    | exact superpose eq633 eq7802
    | (have j0 := eq7802 X0
       grind)
    | exact resolve eq7802 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7802
  have eq7804 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq7803 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq7803
    | (have j0 := eq7803 X0
       grind)
    | exact resolve eq7803 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7803
  have eq7805 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7804 X0
       have i₂ := eq633 (M.op X0 X0)
       grind)
    | exact superpose eq633 eq7804
    | (have j0 := eq7804 X0
       grind)
    | exact resolve eq7804 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7804
  have eq14558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq90 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq90
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
    | exact superpose eq14606 eq121
    | exact resolve eq121 eq14606
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
  have eq14674 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ (k x X0) = (M.op x X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq14649
       grind)
    | exact superpose eq14649 eq14
    | (have j0 := eq14 x X0
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
  have eq14971 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  have eq14978 : (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ y)))) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14698 eq7805
    | exact resolve eq7805 eq14698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7805 eq14698
  have eq14979 : (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) y)) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq14978
    | exact resolve eq14978 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14978
  have eq14981 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq14971
    | exact resolve eq14971 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14971
  have eq14991 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq14979
    | exact resolve eq14979 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14979
  have eq14995 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14991
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14991
    | exact resolve eq14991 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14991
  have eq14997 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq14995
    | exact resolve eq14995 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14995
  have eq14999 : (τ (σ x)) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq121 eq14997
    | exact resolve eq14997 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14997
  have eq15000 : x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq14999
    | exact resolve eq14999 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14999
  have eq15001 : x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ y)) = (τ (M.op (σ y) (σ y))) := by grind
  clear eq15000
  have eq15002 : (τ (σ y)) = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq121 eq15001
    | exact resolve eq15001 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15001
  have eq15003 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq15002
    | exact resolve eq15002 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15002
  have eq19150 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq529 x X0
       have i₂ := eq14649
       grind)
    | exact superpose eq14649 eq529
    | (have j0 := eq529 x X0
       grind)
    | exact resolve eq529 eq14649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq14649
  have eq19186 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq19150 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq19150
    | (have j0 := eq19150 X0
       grind)
    | exact resolve eq19150 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19150
  have eq19194 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq19186 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19186
    | (have j0 := eq19186 X0
       grind)
    | exact resolve eq19186 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19186
  have eq21181 : ∀ X0 : G, y ≠ (τ (M.op X0 X0)) ∨ (k x (τ X0)) = (M.op x (τ X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14674 (τ X0)
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq14674
    | (have j0 := eq14674 (τ X0)
       grind)
    | exact resolve eq14674 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq14674
  have eq21195 : ∀ X0 : G, y ≠ (τ (M.op X0 X0)) ∨ (M.op x (τ X0)) = (τ (k (σ x) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq21181 X0
       have i₂ := eq243 X0
       grind)
    | exact superpose eq243 eq21181
    | (have j0 := eq21181 X0
       grind)
    | exact resolve eq21181 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq21181
  have eq60312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14981 eq15003
    | exact resolve eq15003 eq14981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14981 eq15003
  have eq60327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq60312
  have eq60330 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq60327
       have r₂ := eq29
       grind)
    | exact resolve eq60327 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60327
  have eq84624 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq60330 eq121
    | exact resolve eq121 eq60330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60330
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
    | exact superpose eq84690 eq121
    | exact resolve eq121 eq84690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq84690
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
  have eq85613 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq84772
       grind)
    | exact superpose eq84772 eq103
    | exact resolve eq103 eq84772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84772
  have eq85676 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85613
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq85613
    | exact resolve eq85613 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85613
  have eq85714 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq85676 eq19194
    | (have j0 := eq19194 (σ y)
       grind)
    | (have r₁ := eq19194 (σ y)
       have r₂ := eq85676
       grind)
    | exact resolve eq19194 eq85676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19194
  have eq85716 : y ≠ (τ (σ y)) ∨ (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq85676 eq21195
    | (have j0 := eq21195 (σ y)
       grind)
    | exact resolve eq21195 eq85676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21195 eq85676
  have eq85729 : y ≠ (τ (σ y)) ∨ (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ x = (M.op y y) := by grind
  clear eq85716
  have eq85731 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq85714
  have eq85732 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq85731
  have eq85748 : (τ (k (σ x) (σ y))) = (M.op x (τ (σ y))) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq85729
       have r₂ := eq31
       grind)
    | exact resolve eq85729 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85729
  have eq85749 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq85732
    | exact resolve eq85732 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85732
  have eq85766 : (M.op x y) = (τ (k (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq85748
    | exact resolve eq85748 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85748
  have eq85770 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq62 eq85766
    | exact resolve eq85766 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq85766
  have eq85771 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85770
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq85770
    | exact resolve eq85770 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85770
  have eq86616 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq85771
       grind)
    | exact superpose eq85771 eq46
    | exact resolve eq46 eq85771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85771
  have eq86649 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq86616
    | exact resolve eq86616 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86616
  have eq86667 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq86649 eq85749
    | exact resolve eq85749 eq86649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85749 eq86649
  have eq86669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq86667
  have eq86673 : x = (M.op y y) := by
    first
    | (have r₁ := eq86669
       have r₂ := eq29
       grind)
    | exact resolve eq86669 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86669
  have eq87387 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq86673
       grind)
    | exact superpose eq86673 eq103
    | exact resolve eq103 eq86673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq87402 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq86673
       grind)
    | exact superpose eq86673 eq14
    | (have j0 := eq14 X0 y
       grind)
    | exact resolve eq14 eq86673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87405 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq528 y X0
       have i₂ := eq86673
       grind)
    | exact superpose eq86673 eq528
    | (have j0 := eq528 y X0
       grind)
    | exact resolve eq528 eq86673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq86673
  have eq87418 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq87405 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87405
    | (have j0 := eq87405 X0
       grind)
    | exact resolve eq87405 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87405
  have eq87433 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq87387
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87387
    | exact resolve eq87387 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87387
  have eq87439 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq87418 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq87418
    | (have j0 := eq87418 X0
       grind)
    | exact resolve eq87418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq87418
  have eq87474 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  have eq87479 : (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ y)))) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq87433 eq6124
    | exact resolve eq6124 eq87433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6124 eq87433
  have eq87498 : (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) y)) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq31 eq87479
    | exact resolve eq87479 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq87479
  have eq87499 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28 eq87474
    | exact resolve eq87474 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87474
  have eq87510 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq30 eq87498
    | exact resolve eq87498 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87498
  have eq87514 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq87510
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq87510
    | exact resolve eq87510 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87510
  have eq87518 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq22 eq87514
    | exact resolve eq87514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87514
  have eq87520 : (τ (σ x)) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq68 eq87518
    | exact resolve eq87518 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87518
  have eq87522 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq87520
    | exact resolve eq87520 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87520
  have eq88211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq87522 eq87499
    | exact resolve eq87499 eq87522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87499 eq87522
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
  have eq89005 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq88213 eq68
    | exact resolve eq68 eq88213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq88213
  have eq89180 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq89005
    | exact resolve eq89005 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq89005
  have eq89181 : x = (M.op x x) := by grind
  clear eq89180
  have eq89185 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq89181
       grind)
    | exact superpose eq89181 eq56
    | exact resolve eq56 eq89181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq89353 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq89185
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq89185
    | exact resolve eq89185 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq89185
  have eq94442 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq87402 x
       have i₂ := eq89181
       grind)
    | exact superpose eq89181 eq87402
    | (have j0 := eq87402 x
       grind)
    | (have r₁ := eq87402 x
       have r₂ := eq89181
       grind)
    | exact resolve eq87402 eq89181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87402 eq89181
  have eq94456 : (M.op x y) = (k x y) := by grind
  clear eq94442
  have eq94459 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq94456
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq94456
    | exact resolve eq94456 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq94456
  have eq95180 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq94459
       grind)
    | exact superpose eq94459 eq46
    | exact resolve eq46 eq94459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq94459
  have eq95209 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq95180
    | exact resolve eq95180 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95180
  have eq98355 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq89353 eq87439
    | (have j0 := eq87439 (σ x)
       grind)
    | (have r₁ := eq87439 (σ x)
       have r₂ := eq89353
       grind)
    | exact resolve eq87439 eq89353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87439 eq89353
  have eq98368 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq98355
  have eq98371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq95209 eq98368
    | exact resolve eq98368 eq95209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95209 eq98368
  have eq98374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq98371
    | exact resolve eq98371 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq98371
  have eq98376 : False := by grind
  exact eq98376

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pxx_y_pyy_x_pyx_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X1 X1)
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
  have eq179 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq29 y x
       grind)
    | exact superpose eq29 eq18
    | (have j1 := eq29 y x
       grind)
    | exact resolve eq18 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq29 sF3 sF2
       grind)
    | exact superpose eq29 eq26
    | (have j1 := eq29 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq193 : (σ y) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq194 : y = (k x x) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) := by
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
  have eq199 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
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
  have eq200 : (M.op x y) = (k y x) ∨ y = (k x x) ∨ x = (k y y) := by
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
  have eq204 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq205 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq1104 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
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
  have eq1109 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
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
  have eq1110 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
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
  have eq1113 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1115 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq1118 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
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
  have eq1119 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
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
  have eq3553 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq200
       grind)
    | exact superpose eq200 eq41
    | exact resolve eq41 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq3554 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq3553
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3553
    | exact resolve eq3553 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq3557 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = (k y y) := by
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
  have eq14315 : ∀ X0 : G, y ≠ (k X0 X0) ∨ (k X0 x) = (M.op x X0) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq205 X0 x
       have i₂ := eq14299
       grind)
    | exact superpose eq14299 eq205
    | (have j0 := eq205 X0 x
       grind)
    | exact resolve eq205 eq14299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14316 : (M.op x y) = (k x y) ∨ y = (k y y) ∨ x = (k y y) := by
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
  have eq14318 : (M.op x y) = (k x y) ∨ y = (k y y) ∨ x = (k y y) := by
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
  have eq14335 : ∀ X0 : G, (σ y) ≠ (k X0 X0) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq14323 eq205
    | (have j0 := eq205 X0 (σ x)
       grind)
    | exact resolve eq205 eq14323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14336 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq14323 eq1110
    | exact resolve eq1110 eq14323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq14323
  have eq14338 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq14336
    | exact resolve eq14336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14336
  have eq14349 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq14318
       grind)
    | exact superpose eq14318 eq42
    | exact resolve eq42 eq14318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14318
  have eq14350 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14349
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14349
    | exact resolve eq14349 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14349
  have eq14354 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k y y) := by
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
  have eq14561 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq14315 y
       have i₂ := eq14399
       grind)
    | exact superpose eq14399 eq14315
    | (have j0 := eq14315 y
       grind)
    | (have r₁ := eq14315 y
       have r₂ := eq14399
       grind)
    | exact resolve eq14315 eq14399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14315 eq14399
  have eq14572 : (M.op x y) = (k y x) ∨ x = y ∨ x = (k y y) := by grind
  clear eq14561
  have eq14575 : (M.op x y) = (k y x) ∨ x = (k y y) := by
    first
    | (have r₁ := eq14572
       have r₂ := eq14416
       grind)
    | exact resolve eq14572 eq14416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14416 eq14572
  have eq14577 : (M.op x y) = (k y x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14575
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14575
    | exact resolve eq14575 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14575
  have eq14601 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq14577
       grind)
    | exact superpose eq14577 eq41
    | exact resolve eq41 eq14577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14577
  have eq14602 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14601
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14601
    | exact resolve eq14601 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14601
  have eq14606 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | exact superpose eq20 eq14602
    | exact resolve eq14602 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14602
  have eq14914 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq14417 eq14335
    | (have j0 := eq14335 (σ y)
       grind)
    | (have r₁ := eq14335 (σ y)
       have r₂ := eq14417
       grind)
    | exact resolve eq14335 eq14417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14335 eq14417
  have eq14920 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y y) := by grind
  clear eq14914
  have eq14921 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y y) := by grind
  clear eq14920
  have eq14927 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq14921
    | exact resolve eq14921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14921
  have eq14930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq14606 eq14927
    | exact resolve eq14927 eq14606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14606 eq14927
  have eq14931 : x = (k y y) := by
    first
    | (have r₁ := eq14930
       have r₂ := eq27
       grind)
    | exact resolve eq14930 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14930
  have eq14936 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq14931
       grind)
    | exact superpose eq14931 eq42
    | exact resolve eq42 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14941 : ∀ X0 : G, x ≠ (k X0 X0) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq205 y X0
       have i₂ := eq14931
       grind)
    | exact superpose eq14931 eq205
    | (have j0 := eq205 y X0
       grind)
    | exact resolve eq205 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14946 : (M.op x y) = (k x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1119 y
       have i₂ := eq14931
       grind)
    | exact superpose eq14931 eq1119
    | exact resolve eq1119 eq14931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14931
  have eq14949 : (M.op x y) = (k x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14946
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14946
    | exact resolve eq14946 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14946
  have eq14950 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14936
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14936
    | exact resolve eq14936 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14936
  have eq14955 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14950
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14950
    | exact resolve eq14950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14950
  have eq14970 : ∀ X0 : G, (σ x) ≠ (k X0 X0) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq14955 eq205
    | (have j0 := eq205 (σ y) X0
       grind)
    | exact resolve eq205 eq14955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq14975 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14955 eq1119
    | exact resolve eq1119 eq14955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq14955
  have eq14981 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq14975
    | exact resolve eq14975 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14975
  have eq14994 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq14949
       grind)
    | exact superpose eq14949 eq42
    | exact resolve eq42 eq14949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq14949
  have eq14995 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14994
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14994
    | exact resolve eq14994 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14994
  have eq14999 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq14995
    | exact resolve eq14995 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14995
  have eq15018 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq14999 eq14981
    | exact resolve eq14981 eq14999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14981 eq14999
  have eq15023 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq15018
       have r₂ := eq27
       grind)
    | exact resolve eq15018 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15018
  have eq15040 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) := by
    first
    | exact superpose eq15023 eq143
    | exact resolve eq143 eq15023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq15023
  have eq15054 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq31 eq15040
    | exact resolve eq15040 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15040
  have eq15055 : x = (k x x) := by grind
  clear eq15054
  have eq15067 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq15055
       grind)
    | exact superpose eq15055 eq41
    | exact resolve eq41 eq15055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15082 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15067
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15067
    | exact resolve eq15067 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15067
  have eq15219 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq14941 x
       have i₂ := eq15055
       grind)
    | exact superpose eq15055 eq14941
    | (have j0 := eq14941 x
       grind)
    | (have r₁ := eq14941 x
       have r₂ := eq15055
       grind)
    | exact resolve eq14941 eq15055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14941 eq15055
  have eq15232 : (M.op x y) = (k y x) := by grind
  clear eq15219
  have eq15235 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq15232
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15232
    | exact resolve eq15232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15232
  have eq15240 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq15235
       grind)
    | exact superpose eq15235 eq41
    | exact resolve eq41 eq15235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq15235
  have eq15241 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq15240
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15240
    | exact resolve eq15240 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15240
  have eq15245 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq15241
    | exact resolve eq15241 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15241
  have eq15813 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq15082 eq14970
    | (have j0 := eq14970 (σ x)
       grind)
    | (have r₁ := eq14970 (σ x)
       have r₂ := eq15082
       grind)
    | exact resolve eq14970 eq15082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14970 eq15082
  have eq15824 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq15813
  have eq15827 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15245 eq15824
    | exact resolve eq15824 eq15245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15245 eq15824
  have eq15830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15827 eq26
    | exact resolve eq26 eq15827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15827
  have eq15832 : False := by grind
  exact eq15832

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyy_pxx_y_pyy_x_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq19 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq16
    | exact resolve eq16 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq19
    | exact resolve eq19 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq22
    | exact resolve eq22 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq67 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq31
    | exact resolve eq31 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq130 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq67
    | exact resolve eq67 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) ≠ (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | (have r₁ := eq177 X0 X0
       have r₂ := eq175 X0
       grind)
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq232 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq130 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq130
    | exact resolve eq130 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq511 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq232
    | exact resolve eq232 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq558 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    grind
  have eq559 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq558 X0
       have i₂ := eq175 (k X0 X0)
       grind)
    | exact superpose eq175 eq558
    | (have j0 := eq558 X0
       grind)
    | exact resolve eq558 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq826 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq511 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq511
    | exact resolve eq511 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq1203 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1203
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1203
    | exact resolve eq1203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1209 : y = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1208
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1208
    | exact resolve eq1208 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1210 : x = (k y y) ∨ y = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1209
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq1209
    | exact resolve eq1209 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1211 : (M.op x x) = (k y y) ∨ x = (k y y) ∨ y = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq1210
    | exact resolve eq1210 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1212 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq1211
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1211
    | exact resolve eq1211 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1288 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (k x x) ∨ (k x x) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1212
       have i₂ := eq11 (σ x) (σ y)
       grind)
    | exact superpose eq11 eq1212
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq1212
       have r₂ := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq1212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1289 : x = (k y y) ∨ y = (k x x) ∨ (k x x) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1288
  have eq1290 : (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ y = (k x x) ∨ (k x x) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1289
       have i₂ := eq175 (σ x)
       grind)
    | exact superpose eq175 eq1289
    | exact resolve eq1289 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1291 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ y = (k x x) ∨ (k x x) = (k y y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1290
       have i₂ := eq175 (σ y)
       grind)
    | exact superpose eq175 eq1290
    | exact resolve eq1290 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1292 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ y = (k x x) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq1291
       have i₂ := eq175 (σ y)
       grind)
    | exact superpose eq175 eq1291
    | exact resolve eq1291 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1293 : y = (k x x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq1292
       have i₂ := eq175 (σ x)
       grind)
    | exact superpose eq175 eq1292
    | exact resolve eq1292 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1370 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq1293
       grind)
    | exact superpose eq1293 eq10
    | exact resolve eq10 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1371 : x = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k x x) = (k y y) := by grind
  clear eq1370
  have eq1453 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1371
       grind)
    | exact superpose eq1371 eq10
    | exact resolve eq10 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1455 : (k x x) = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq1453
  have eq1538 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1455
       grind)
    | exact superpose eq1455 eq10
    | exact resolve eq10 eq1455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455
  have eq1540 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1538
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1538
    | exact resolve eq1538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1541 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq1540
  have eq1627 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq1541
       grind)
    | exact superpose eq1541 eq19
    | exact resolve eq19 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1681 : (k x x) = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1627
       have i₂ := eq19 x x
       grind)
    | exact superpose eq19 eq1627
    | exact resolve eq1627 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq2252 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq826 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq826
    | exact resolve eq826 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq2630 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq178 y x
       grind)
    | exact superpose eq178 eq9
    | (have j1 := eq178 x y
       grind)
    | exact resolve eq9 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2634 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq2630
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq2630
    | exact resolve eq2630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630
  have eq2646 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k x x) ≠ (k y y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2634
       have i₂ := eq178 (σ y) (σ x)
       grind)
    | exact superpose eq178 eq2634
    | (have j1 := eq178 x y
       grind)
    | (have r₁ := eq2634
       have r₂ := eq178 (σ y) (σ x)
       grind)
    | exact resolve eq2634 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2648 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k x x) ≠ (k y y) := by grind
  clear eq2646
  have eq2654 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) ≠ (k X0 X0) := by
    intro X0
    grind
  clear eq178
  have eq2655 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2654 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq2656 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2655 X0
       have i₂ := eq175 (k X0 X0)
       grind)
    | exact superpose eq175 eq2655
    | (have j0 := eq2655 X0
       grind)
    | exact resolve eq2655 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq2658 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2656 X0
       have i₂ := eq175 (k X0 X0)
       grind)
    | exact superpose eq175 eq2656
    | (have j0 := eq2656 X0
       grind)
    | exact resolve eq2656 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2656
  have eq2660 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k x x) ≠ (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2648
       have i₂ := eq1541
       grind)
    | exact superpose eq1541 eq2648
    | (have r₁ := eq2648
       have r₂ := eq1541
       grind)
    | exact resolve eq2648 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq2661 : (k x x) ≠ (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq2660
  have eq2662 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq2661
       have r₂ := eq1681
       grind)
    | exact resolve eq2661 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681 eq2661
  have eq2663 : (k x x) = (τ (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq19 x x
       have i₂ := eq2662
       grind)
    | exact superpose eq2662 eq19
    | exact resolve eq19 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2726 : y = (k x x) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2663
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq2663
    | exact resolve eq2663 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq5165 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2252 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2252
    | exact resolve eq2252 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2252
  have eq16332 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5165 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5165
    | exact resolve eq5165 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5165
  have eq26812 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16332 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq16332
    | exact resolve eq16332 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16332
  have eq70202 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2658 (σ x)
       have i₂ := eq2662
       grind)
    | exact superpose eq2662 eq2658
    | exact resolve eq2658 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70267 : (M.op x y) = (k y x) ∨ x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2658 x
       have i₂ := eq2726
       grind)
    | exact superpose eq2726 eq2658
    | exact resolve eq2658 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2658
  have eq70277 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq70202
  have eq70992 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq70267
       grind)
    | exact superpose eq70267 eq9
    | exact resolve eq9 eq70267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70267
  have eq70995 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq70992
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq70992
    | exact resolve eq70992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70992
  have eq71675 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k x x) ≠ (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2634
       have i₂ := eq70277
       grind)
    | exact superpose eq70277 eq2634
    | (have r₁ := eq2634
       have r₂ := eq70277
       grind)
    | exact resolve eq2634 eq70277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71678 : (k x x) ≠ (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq71675
  have eq71680 : y ≠ (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2726 eq71678
    | exact resolve eq71678 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71678
  have eq73042 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq70995
       have i₂ := eq70277
       grind)
    | exact superpose eq70277 eq70995
    | (have r₁ := eq70995
       have r₂ := eq70277
       grind)
    | exact resolve eq70995 eq70277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70277 eq70995
  have eq73046 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq73042
  have eq73047 : x = (k y y) ∨ y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq73046
  have eq73050 : x = (k y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq73047
       have r₂ := eq71680
       grind)
    | exact resolve eq73047 eq71680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71680 eq73047
  have eq73740 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq73050
       grind)
    | exact superpose eq73050 eq10
    | exact resolve eq10 eq73050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73050
  have eq73741 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq73740
  have eq73750 : (σ y) ≠ (k (σ x) (σ x)) ∨ (k x x) ≠ (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2648
       have i₂ := eq73741
       grind)
    | exact superpose eq73741 eq2648
    | exact resolve eq2648 eq73741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73883 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq26812 y (σ y)
       have i₂ := eq73741
       grind)
    | exact superpose eq73741 eq26812
    | exact resolve eq26812 eq73741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73741
  have eq73892 : y = (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq73883
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq73883
    | exact resolve eq73883 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73883
  have eq74023 : (k x x) ≠ (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq73750
       have r₂ := eq2662
       grind)
    | exact resolve eq73750 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662 eq73750
  have eq74024 : y ≠ (k y y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2726 eq74023
    | exact resolve eq74023 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2726 eq74023
  have eq74025 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq74024
       have r₂ := eq73892
       grind)
    | exact resolve eq74024 eq73892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73892 eq74024
  have eq74028 : (σ x) ≠ (k (σ x) (σ x)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq2648
       have i₂ := eq74025
       grind)
    | exact superpose eq74025 eq2648
    | exact resolve eq2648 eq74025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq74029 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq74025
       grind)
    | exact superpose eq74025 eq19
    | exact resolve eq19 eq74025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq74162 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq559 (σ y)
       have i₂ := eq74025
       grind)
    | exact superpose eq74025 eq559
    | exact resolve eq559 eq74025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74025
  have eq74295 : x = (k y y) := by
    first
    | (have i₁ := eq74029
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq74029
    | exact resolve eq74029 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74029
  have eq74296 : (k x x) ≠ (k y y) := by grind
  clear eq2634 eq74028
  have eq74419 : x ≠ (k x x) := by
    first
    | (have i₁ := eq74296
       have i₂ := eq74295
       grind)
    | exact superpose eq74295 eq74296
    | exact resolve eq74296 eq74295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74296
  have eq74426 : x = (k x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq559 y
       have i₂ := eq74295
       grind)
    | exact superpose eq74295 eq559
    | exact resolve eq559 eq74295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq74295
  have eq74429 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq74426
       have r₂ := eq74419
       grind)
    | exact resolve eq74426 eq74419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74426
  have eq77892 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq74429
       grind)
    | exact superpose eq74429 eq9
    | exact resolve eq9 eq74429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74429
  have eq77895 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77892
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq77892
    | exact resolve eq77892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77892
  have eq77898 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq74162
       have r₂ := eq77895
       grind)
    | exact resolve eq74162 eq77895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74162 eq77895
  have eq78038 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | (have i₁ := eq26812 x (σ x)
       have i₂ := eq77898
       grind)
    | exact superpose eq77898 eq26812
    | exact resolve eq26812 eq77898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26812 eq77898
  have eq78045 : x = (k x x) := by
    first
    | (have i₁ := eq78038
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq78038
    | exact resolve eq78038 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78038
  have eq78180 : False := by grind
  exact eq78180
