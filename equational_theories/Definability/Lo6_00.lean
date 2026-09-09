import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pxx_pyx_pyx_pyy_pyx_pyy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
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
  clear eq24 eq38
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
  clear eq40 eq41
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
  have eq48 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (τ (k (k (σ X0) (σ X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (k X0 X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 (M.op x y) X0
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (k X2 (k X0 X1)) = (τ (k (σ X2) (k (σ X0) (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 X2 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 (M.op x y)
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq73 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq73 X0
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq56
    | exact resolve eq56 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq13
    | (have j0 := eq13 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq13 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq74 sF4
       grind)
    | exact superpose eq74 eq93
    | exact resolve eq93 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq96 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq92
       have i₂ := eq74 (τ sF4)
       grind)
    | exact superpose eq74 eq92
    | exact resolve eq92 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq98 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq74 sF5
       grind)
    | exact superpose eq74 eq95
    | exact resolve eq95 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq96
       have i₂ := eq74 (τ sF5)
       grind)
    | exact superpose eq74 eq96
    | exact resolve eq96 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq101 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq74 sF5
       grind)
    | exact superpose eq74 eq98
    | exact resolve eq98 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq74 (τ sF5)
       grind)
    | exact superpose eq74 eq99
    | exact resolve eq99 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq104 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq74 sF5
       grind)
    | exact superpose eq74 eq101
    | exact resolve eq101 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq74 (τ sF5)
       grind)
    | exact superpose eq74 eq102
    | exact resolve eq102 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq121 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq138 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq14
    | (have j0 := eq14 (τ (σ y)) x
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq151 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq157 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq150 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq150 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq150 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq150 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq150 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq158 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq151 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq151 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq159 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq74 sF5
       grind)
    | exact superpose eq74 eq140
    | exact resolve eq140 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq161 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq74 (τ sF5)
       grind)
    | exact superpose eq74 eq138
    | exact resolve eq138 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq167 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | (have r₁ := eq157 X0 X0
       have r₂ := eq74 X0
       grind)
    | exact resolve eq157 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq168 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq158
    | (have j0 := eq158 X0 X1
       grind)
    | (have r₁ := eq158 X0 X0
       have r₂ := eq74 X0
       grind)
    | exact resolve eq158 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq169 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq159
       have i₂ := eq74 sF4
       grind)
    | exact superpose eq74 eq159
    | exact resolve eq159 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq171 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq161
       have i₂ := eq74 (τ sF4)
       grind)
    | exact superpose eq74 eq161
    | exact resolve eq161 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq177 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq178 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq168
    | (have j0 := eq168 X0 X1
       grind)
    | exact resolve eq168 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq179 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq169
       have i₂ := eq74 sF5
       grind)
    | exact superpose eq74 eq169
    | exact resolve eq169 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq181 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq171
       have i₂ := eq74 (τ sF5)
       grind)
    | exact superpose eq74 eq171
    | exact resolve eq171 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq187 : ∀ X0 X1 : G, (k X0 X1) = (k X1 X1) ∨ (k X0 X0) = X0 ∨ (k X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq188 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X1) = (k X0 X0) ∨ (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq178
    | (have j0 := eq178 X0 X1
       grind)
    | exact resolve eq178 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq193 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq187
    | (have j0 := eq187 X0 X1
       grind)
    | exact resolve eq187 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq194 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X0) = X0 ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq254 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq11
    | (have j0 := eq11 X0 X1
       grind)
    | exact resolve eq11 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq254
    | (have j0 := eq254 X0 X1
       grind)
    | (have r₁ := eq254 X0 X0
       have r₂ := eq74 X0
       grind)
    | exact resolve eq254 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq254
  have eq326 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq179 eq33
    | exact resolve eq33 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  have eq457 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq181 eq15
    | exact resolve eq15 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq457
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq457
    | exact resolve eq457 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq468 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq459 eq15
    | exact resolve eq15 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq474 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq468
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq468
    | exact resolve eq468 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq477 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq474
    | exact resolve eq474 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq480 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq477 eq15
    | exact resolve eq15 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq480
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq480
    | exact resolve eq480 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq482 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq481
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq481
    | exact resolve eq481 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq483 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq482
    | exact resolve eq482 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq492 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq483 eq15
    | exact resolve eq15 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq492
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq492
    | exact resolve eq492 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq500 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq497
    | exact resolve eq497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq502 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq500 eq121
    | exact resolve eq121 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq502 eq255
    | (have j0 := eq255 (τ (σ y)) X0
       grind)
    | (have r₁ := eq255 (τ (σ y)) x
       have r₂ := eq502
       grind)
    | exact resolve eq255 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq540 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq181 eq255
    | (have j0 := eq255 (τ (σ y)) X0
       grind)
    | (have r₁ := eq255 (τ (σ y)) x
       have r₂ := eq181
       grind)
    | exact resolve eq255 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq542 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq500 eq255
    | (have j0 := eq255 (σ y) X0
       grind)
    | (have r₁ := eq255 (σ y) x
       have r₂ := eq500
       grind)
    | exact resolve eq255 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq545 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq542 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq546 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | (have j0 := eq540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq547 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq554 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq545 eq32
    | (have j1 := eq545 (σ x)
       grind)
    | exact resolve eq32 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq564 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq179 eq554
    | exact resolve eq554 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq568 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq564
       have r₂ := eq328
       grind)
    | exact resolve eq564 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq564
  have eq569 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq568
       have r₂ := eq326
       grind)
    | exact resolve eq568 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq572 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq256
    | (have j0 := eq256 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq256 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq256
    | (have j0 := eq256 (σ y) (σ x)
       grind)
    | exact resolve eq256 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq672 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq547 eq42
    | exact resolve eq42 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq702 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq672 eq15
    | exact resolve eq15 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq703 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq702
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq702
    | exact resolve eq702 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq704 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq703
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq703
    | exact resolve eq703 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq705 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq704
    | exact resolve eq704 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq706 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq705
  have eq707 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq706 eq36
    | exact resolve eq36 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  have eq726 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq707
       have i₂ := eq121 sF5 sF5
       grind)
    | exact superpose eq121 eq707
    | exact resolve eq707 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq741 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq483 eq105
    | (have r₁ := eq105
       have r₂ := eq483
       grind)
    | exact resolve eq105 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq742 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq741
  have eq747 : ∀ X0 : G, (M.op x y) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq726 eq255
    | (have j0 := eq255 (τ (σ y)) X0
       grind)
    | exact resolve eq255 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq785 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq179 eq574
    | (have r₁ := eq574
       have r₂ := eq179
       grind)
    | exact resolve eq574 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq786 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq785
  have eq787 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq786
  have eq863 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq546 eq42
    | exact resolve eq42 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq864 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq863
  have eq871 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq864 eq572
    | (have r₁ := eq572
       have r₂ := eq864
       grind)
    | exact resolve eq572 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq864 eq15
    | exact resolve eq15 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq885 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq871
  have eq887 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq880
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq880
    | exact resolve eq880 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq890 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq887
    | exact resolve eq887 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq894 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq890 eq15
    | exact resolve eq15 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq895 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq894
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq894
    | exact resolve eq894 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq896 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq895
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq895
    | exact resolve eq895 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq897 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq896
    | exact resolve eq896 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq906 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq897 eq105
    | (have r₁ := eq105
       have r₂ := eq897
       grind)
    | exact resolve eq105 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq897
  have eq920 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq906
  have eq1043 : (k (τ (σ y)) (τ (σ x))) = (τ (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq787 eq121
    | exact resolve eq121 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq1050 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq121 sF4 sF4
       grind)
    | exact superpose eq121 eq1043
    | exact resolve eq1043 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1118 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1050 eq477
    | exact resolve eq477 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1119 : (k (τ (σ x)) (τ (σ x))) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1050 eq194
    | (have j0 := eq194 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq194 (τ (σ y)) (τ (σ x))
       have r₂ := eq1050
       grind)
    | exact resolve eq194 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1124 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1119
  have eq1125 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1118
  have eq1132 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq1124
    | exact resolve eq1124 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1133 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1125
       have r₂ := eq326
       grind)
    | exact resolve eq1125 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1316 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1133 eq15
    | exact resolve eq15 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1316
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1316
    | exact resolve eq1316 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1325 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1322
    | exact resolve eq1322 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1350 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1325 eq33
    | exact resolve eq33 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1351 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1325
  have eq2172 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq885 eq15
    | exact resolve eq15 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq2180 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2172
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq2172
    | exact resolve eq2172 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172
  have eq2185 : (k (σ x) (σ x)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2180
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2180
    | exact resolve eq2180 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2187 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2185
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2185
    | exact resolve eq2185 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185
  have eq3196 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2187 eq15
    | exact resolve eq15 eq2187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187
  have eq3201 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3196
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq3196
    | exact resolve eq3196 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq3202 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3201
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq3201
    | exact resolve eq3201 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq3203 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3202
    | exact resolve eq3202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3202
  have eq3231 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1132
  have eq3242 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3231
       have r₂ := eq1133
       grind)
    | exact resolve eq3231 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq3231
  have eq3259 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3203 eq15
    | exact resolve eq15 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3265 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3259
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq3259
    | exact resolve eq3259 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259
  have eq3268 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3265
    | exact resolve eq3265 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3265
  have eq3269 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3268 eq1351
    | (have r₁ := eq1351
       have r₂ := eq3268
       grind)
    | exact resolve eq1351 eq3268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3270 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3268 eq194
    | (have j0 := eq194 (σ y) (σ x)
       grind)
    | (have r₁ := eq194 (σ y) (σ x)
       have r₂ := eq3268
       grind)
    | exact resolve eq194 eq3268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq3268
  have eq3275 : (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq3270
  have eq3276 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq3269
  have eq3277 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq3276
  have eq3281 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq3275
       have r₂ := eq716
       grind)
    | exact resolve eq3275 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275
  have eq3282 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq3277
       have r₂ := eq1350
       grind)
    | exact resolve eq3277 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3277
  have eq3284 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq3281
    | exact resolve eq3281 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq3328 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3284 eq3282
    | exact resolve eq3282 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282 eq3284
  have eq3329 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq3328
  have eq3337 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3329
       have r₂ := eq716
       grind)
    | exact resolve eq3329 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq3329
  have eq3362 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3337 eq121
    | exact resolve eq121 eq3337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337
  have eq3531 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq3362 eq255
    | (have j0 := eq255 (τ (σ y)) X0
       grind)
    | (have r₁ := eq255 (τ (σ y)) x
       have r₂ := eq3362
       grind)
    | exact resolve eq255 eq3362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq3536 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3531
  have eq3552 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3536 X0
       have j1 := eq747 X0
       grind)
    | (have r₁ := eq3536 X0
       have r₂ := eq747 X0
       grind)
    | exact resolve eq3536 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq3536
  have eq3670 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3552 eq42
    | exact resolve eq42 eq3552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3690 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3670 eq15
    | exact resolve eq15 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq3693 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3690
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq3690
    | exact resolve eq3690 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690
  have eq3695 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3693
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq3693
    | exact resolve eq3693 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq3696 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq3695
    | exact resolve eq3695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695
  have eq3697 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq3696
  have eq3716 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3697 eq36
    | exact resolve eq36 eq3697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3725 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3697 eq1350
    | (have r₁ := eq1350
       have r₂ := eq3697
       grind)
    | exact resolve eq1350 eq3697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq3726 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  have eq3727 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq3725
  have eq3728 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq3727
       have r₂ := eq1351
       grind)
    | exact resolve eq3727 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351 eq3727
  have eq3736 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3716
       have i₂ := eq121 sF4 sF5
       grind)
    | exact superpose eq121 eq3716
    | exact resolve eq3716 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq3772 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3728 eq104
    | (have r₁ := eq104
       have r₂ := eq3728
       grind)
    | exact resolve eq104 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3774 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3728 eq574
    | exact resolve eq574 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728
  have eq3779 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq3774
  have eq3781 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq3772
  have eq3782 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq3781
  have eq3789 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq3779
       have r₂ := eq3726
       grind)
    | exact resolve eq3779 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726 eq3779
  have eq5074 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3242 eq15
    | exact resolve eq15 eq3242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq5080 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5074
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq5074
    | exact resolve eq5074 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5074
  have eq5081 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq5080
  have eq10320 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ y)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq742 eq15
    | exact resolve eq15 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq10354 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10320
       have i₂ := eq15 (τ sF5) (τ sF4)
       grind)
    | exact superpose eq15 eq10320
    | exact resolve eq10320 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10320
  have eq10360 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10354
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq10354
    | exact resolve eq10354 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10354
  have eq10361 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10360
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq10360
    | exact resolve eq10360 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10360
  have eq10703 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq5081 eq15
    | exact resolve eq15 eq5081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5081
  have eq10731 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10703
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq10703
    | exact resolve eq10703 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10703
  have eq10732 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq10731
    | exact resolve eq10731 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10731
  have eq10733 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq10732
       have r₂ := eq326
       grind)
    | exact resolve eq10732 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq10732
  have eq10736 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq10733 eq33
    | exact resolve eq33 eq10733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10738 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq10733 eq574
    | exact resolve eq574 eq10733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq10742 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq10733
  have eq10746 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq10738
  have eq10752 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq10746
       have r₂ := eq10742
       grind)
    | exact resolve eq10746 eq10742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10746
  have eq36294 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ y)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq920 eq15
    | exact resolve eq15 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq36328 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36294
       have i₂ := eq15 (τ sF5) (τ sF4)
       grind)
    | exact superpose eq15 eq36294
    | exact resolve eq36294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36294
  have eq36334 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36328
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq36328
    | exact resolve eq36328 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36328
  have eq36335 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36334
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq36334
    | exact resolve eq36334 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36334
  have eq38188 : (σ y) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq3782
  have eq38215 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq38188
       have r₂ := eq3789
       grind)
    | exact resolve eq38188 eq3789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38188
  have eq40195 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq10361 eq15
    | exact resolve eq15 eq10361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10361
  have eq40226 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40195
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq40195
    | exact resolve eq40195 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40195
  have eq40227 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq40226
  have eq133894 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq40227 eq15
    | exact resolve eq15 eq40227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40227
  have eq133958 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq133894
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq133894
    | exact resolve eq133894 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133894
  have eq133959 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq133958
    | exact resolve eq133958 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133958
  have eq133960 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq133959
  have eq133990 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq133960 eq10752
    | (have r₁ := eq10752
       have r₂ := eq133960
       grind)
    | exact resolve eq10752 eq133960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134015 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq133960
  have eq134022 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq133990
  have eq134056 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq134022
       have r₂ := eq10736
       grind)
    | exact resolve eq134022 eq10736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134022
  have eq134113 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq569 eq134056
    | exact resolve eq134056 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq134118 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq134056 eq33
    | exact resolve eq33 eq134056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134056
  have eq134132 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq134113
  have eq134139 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq134132
       have r₂ := eq134118
       grind)
    | exact resolve eq134132 eq134118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134118 eq134132
  have eq134143 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq134139
       have r₂ := eq134015
       grind)
    | exact resolve eq134139 eq134015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134015 eq134139
  have eq134145 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq134143
       have r₂ := eq10742
       grind)
    | exact resolve eq134143 eq10742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10742 eq134143
  have eq134146 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq134145
       have r₂ := eq10736
       grind)
    | exact resolve eq134145 eq10736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134145
  have eq134154 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq134146 eq33
    | exact resolve eq33 eq134146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134155 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq134146 eq104
    | (have r₁ := eq104
       have r₂ := eq134146
       grind)
    | exact resolve eq104 eq134146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq134146
  have eq134163 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq134155
  have eq134164 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq134163
  have eq134238 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq36335 eq255
    | (have j0 := eq255 (τ (σ y)) X0
       grind)
    | (have r₁ := eq255 (τ (σ y)) x
       have r₂ := eq36335
       grind)
    | exact resolve eq255 eq36335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36335
  have eq134261 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq134238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134238
  have eq134559 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ y) (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq134164 eq121
    | exact resolve eq121 eq134164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134164
  have eq134596 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq134559
       have i₂ := eq121 sF4 sF5
       grind)
    | exact superpose eq121 eq134559
    | exact resolve eq134559 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134559
  have eq227302 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq134261 eq42
    | exact resolve eq42 eq134261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134261
  have eq453057 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq227302 eq15
    | exact resolve eq15 eq227302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227302
  have eq453144 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq453057
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq453057
    | exact resolve eq453057 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453057
  have eq453145 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq453144
    | exact resolve eq453144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453144
  have eq453146 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq453145
  have eq453371 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq453146 eq15
    | exact resolve eq15 eq453146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453146
  have eq453459 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq453371
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq453371
    | exact resolve eq453371 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453371
  have eq453461 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq453459
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq453459
    | exact resolve eq453459 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453459
  have eq453462 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq453461
    | exact resolve eq453461 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453461
  have eq453463 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq453462
  have eq453508 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq453463 eq10752
    | (have r₁ := eq10752
       have r₂ := eq453463
       grind)
    | exact resolve eq10752 eq453463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10752
  have eq453535 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq453463 eq121
    | exact resolve eq121 eq453463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453463
  have eq453594 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq453508
  have eq453636 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq453535
       have i₂ := eq121 sF4 sF5
       grind)
    | exact superpose eq121 eq453535
    | exact resolve eq453535 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453535
  have eq453724 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq453594 eq33
    | exact resolve eq33 eq453594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453594
  have eq453739 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq453724
       have r₂ := eq706
       grind)
    | exact resolve eq453724 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq453724
  have eq454042 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq453739 eq121
    | exact resolve eq121 eq453739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453739
  have eq457415 : ∀ X0 : G, (τ (σ y)) ≠ (k (τ (σ y)) (τ (σ x))) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq453636 eq255
    | (have j0 := eq255 (τ (σ y)) X0
       grind)
    | exact resolve eq255 eq453636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453636
  have eq457532 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq457415 X0
       grind)
    | (have r₁ := eq457415 X0
       have r₂ := eq454042
       grind)
    | exact resolve eq457415 eq454042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454042 eq457415
  have eq457793 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq457532 eq42
    | exact resolve eq42 eq457532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457532
  have eq458032 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq457793 eq15
    | exact resolve eq15 eq457793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457793
  have eq458122 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq458032
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq458032
    | exact resolve eq458032 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458032
  have eq458124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq458122
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq458122
    | exact resolve eq458122 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458122
  have eq458125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq458124
    | exact resolve eq458124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458124
  have eq458126 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq458125
  have eq458127 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq458126 eq36
    | exact resolve eq36 eq458126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458128 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (k (σ y) (σ y)) (σ X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq458126 eq51
    | exact resolve eq51 eq458126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq458129 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq458126 eq56
    | exact resolve eq56 eq458126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq458176 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq458126 eq3697
    | exact resolve eq3697 eq458126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq458925 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq458126
  have eq459191 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq458176
       have r₂ := eq458925
       grind)
    | exact resolve eq458176 eq458925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458176
  have eq459234 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq458129 x
       have i₂ := eq52 (k sF5 sF5) x
       grind)
    | exact superpose eq52 eq458129
    | exact resolve eq458129 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq458129
  have eq459235 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (k (σ y) (σ y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq458128 x
       have i₂ := eq47 (k sF5 sF5) x
       grind)
    | exact superpose eq47 eq458128
    | exact resolve eq458128 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq458128
  have eq459236 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq458127
       have i₂ := eq121 sF5 sF5
       grind)
    | exact superpose eq121 eq458127
    | exact resolve eq458127 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458127
  have eq459311 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq459234 X0
       have i₂ := eq121 sF5 sF5
       grind)
    | exact superpose eq121 eq459234
    | exact resolve eq459234 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459234
  have eq459312 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (τ (σ y)) (τ (σ y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq459235 X0
       have i₂ := eq121 sF5 sF5
       grind)
    | exact superpose eq121 eq459235
    | exact resolve eq459235 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459235
  have eq459461 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459191 eq458925
    | exact resolve eq458925 eq459191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458925
  have eq459479 : (k (σ (σ y)) (σ (σ y))) = (σ (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459191 eq15
    | exact resolve eq15 eq459191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459480 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459191 eq121
    | exact resolve eq121 eq459191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459533 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq459461
  have eq459585 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq459480
       have i₂ := eq121 sF4 sF4
       grind)
    | exact superpose eq121 eq459480
    | exact resolve eq459480 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459480
  have eq459586 : (k (σ (σ y)) (σ (σ y))) = (k (σ (σ x)) (σ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq459479
       have i₂ := eq15 sF4 sF4
       grind)
    | exact superpose eq15 eq459479
    | exact resolve eq459479 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459479
  have eq459613 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459236 eq572
    | (have r₁ := eq572
       have r₂ := eq459236
       grind)
    | exact resolve eq572 eq459236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459728 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq459613
  have eq461048 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (k (τ (σ y)) (τ (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq459311 eq15
    | exact resolve eq15 eq459311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459311
  have eq461586 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ (τ (σ y))) (σ (τ (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq461048 X0
       have i₂ := eq15 (τ sF5) (τ sF5)
       grind)
    | exact superpose eq15 eq461048
    | exact resolve eq461048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461048
  have eq461590 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq461586 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq461586
    | exact resolve eq461586 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461586
  have eq461591 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (k (σ X0) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq461590 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq461590
    | exact resolve eq461590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461590
  have eq461592 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (k (σ X0) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq461591
    | (have j0 := eq461591 X0
       grind)
    | exact resolve eq461591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461591
  have eq461818 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (k (τ (σ y)) (τ (σ y)))) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq459312 eq15
    | exact resolve eq15 eq459312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462391 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ (τ (σ y))) (σ (τ (σ y)))) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq461818 X0
       have i₂ := eq15 (τ sF5) (τ sF5)
       grind)
    | exact superpose eq15 eq461818
    | exact resolve eq461818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461818
  have eq462396 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ y) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq462391 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq462391
    | exact resolve eq462391 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462391
  have eq462397 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (k (k (σ y) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq462396 x
       have i₂ := eq15 sF2 x
       grind)
    | exact superpose eq15 eq462396
    | exact resolve eq462396 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462396
  have eq462398 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (k (k (σ y) (σ y)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq462397
    | (have j0 := eq462397 X0
       grind)
    | exact resolve eq462397 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462397
  have eq462426 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459585 eq572
    | exact resolve eq572 eq459585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462465 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459585 eq459236
    | exact resolve eq459236 eq459585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459236
  have eq462467 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (τ (σ x)) (τ (σ x))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq459585 eq459312
    | exact resolve eq459312 eq459585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459585
  have eq462561 : ∀ X0 : G, (k (M.op x y) X0) = (k (k (τ (σ x)) (τ (σ x))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq462467 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462467
  have eq462563 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq462465
  have eq462620 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq462426
       have r₂ := eq462563
       grind)
    | exact resolve eq462426 eq462563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462426 eq462563
  have eq463164 : ∀ X0 : G, (k X0 (k (σ y) (σ y))) = (τ (k (σ X0) (k (σ (σ x)) (σ (σ x))))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq459586 eq53
    | exact resolve eq53 eq459586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459586
  have eq463260 : ∀ X0 : G, (k X0 (k (σ y) (σ y))) = (k X0 (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq463164 x
       have i₂ := eq53 sF4 sF4 x
       grind)
    | exact superpose eq53 eq463164
    | exact resolve eq463164 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq463164
  have eq463266 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq461592 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq461592
    | exact resolve eq461592 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461592
  have eq465618 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ y) (σ y)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq462398 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq462398
    | exact resolve eq462398 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462398
  have eq466981 : (k (k (σ y) (σ y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq465618 eq463266
    | exact resolve eq463266 eq465618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463266 eq465618
  have eq466994 : (k (k (σ y) (σ y)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq466981
  have eq467891 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (k (τ (σ x)) (τ (σ x)))) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq462561 eq15
    | exact resolve eq15 eq462561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462561
  have eq468442 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ (τ (σ x))) (σ (τ (σ x)))) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq467891 X0
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq467891
    | exact resolve eq467891 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467891
  have eq468447 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (k (σ x) (σ x)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq468442 X0
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq468442
    | exact resolve eq468442 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468442
  have eq468448 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (k (k (σ x) (σ x)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq468447 x
       have i₂ := eq15 sF2 x
       grind)
    | exact superpose eq15 eq468447
    | exact resolve eq468447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468447
  have eq468449 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (k (k (σ x) (σ x)) (σ X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq468448
    | (have j0 := eq468448 X0
       grind)
    | exact resolve eq468448 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468448
  have eq471310 : (k (k (σ x) (σ x)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459191 eq466994
    | exact resolve eq466994 eq459191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466994
  have eq471447 : (k (k (σ x) (σ x)) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq471310
  have eq471673 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ x) (σ x)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq468449 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq468449
    | exact resolve eq468449 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468449
  have eq472965 : (k (k (σ x) (σ x)) (k (σ y) (σ y))) = (k (σ (M.op x y)) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq471673 eq463260
    | exact resolve eq463260 eq471673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463260
  have eq473119 : (k (k (σ x) (σ x)) (k (σ y) (σ y))) = (k (σ (M.op x y)) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq472965
  have eq521524 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459728 eq15
    | exact resolve eq15 eq459728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459728
  have eq521622 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq521524
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq521524
    | exact resolve eq521524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521524
  have eq521623 : (k (σ x) (σ x)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq521622
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq521622
    | exact resolve eq521622 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521622
  have eq521624 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq521623
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq521623
    | exact resolve eq521623 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521623
  have eq521625 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq521624
       have r₂ := eq459533
       grind)
    | exact resolve eq521624 eq459533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521624
  have eq521846 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq521625 eq10736
    | (have r₁ := eq10736
       have r₂ := eq521625
       grind)
    | exact resolve eq10736 eq521625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10736 eq521625
  have eq522242 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq521846
  have eq522906 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq522242 eq33
    | exact resolve eq33 eq522242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522242
  have eq751655 : ∀ X0 : G, (k (τ (σ y)) X0) ≠ (k (τ (σ y)) (τ (σ x))) ∨ (k (τ (σ y)) X0) = (k X0 X0) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (k X0 X0) = (M.op X0 (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq134596 eq193
    | (have j0 := eq193 (τ (σ y)) X0
       grind)
    | (have r₁ := eq193 (τ (σ y)) (τ (σ x))
       have r₂ := eq134596
       grind)
    | exact resolve eq193 eq134596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq134596
  have eq846933 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have j0 := eq751655 (τ (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751655
  have eq846982 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq42 eq846933
    | exact resolve eq846933 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846933
  have eq900392 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq846982 eq3736
    | exact resolve eq3736 eq846982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736 eq846982
  have eq900724 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq900392
  have eq900806 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq900724
       have r₂ := eq3789
       grind)
    | exact resolve eq900724 eq3789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789 eq900724
  have eq900858 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq900806
       have r₂ := eq134154
       grind)
    | exact resolve eq900806 eq134154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900806
  have eq924642 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq462620 eq15
    | exact resolve eq15 eq462620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462620
  have eq924769 : (k (σ (τ (σ y))) (σ (τ (σ x)))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq924642
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq924642
    | exact resolve eq924642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924642
  have eq924770 : (k (σ x) (σ x)) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq924769
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq924769
    | exact resolve eq924769 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924769
  have eq924771 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq924770
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq924770
    | exact resolve eq924770 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924770
  have eq924772 : (τ (σ y)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq924771
       have r₂ := eq459533
       grind)
    | exact resolve eq924771 eq459533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459533 eq924771
  have eq926080 : (σ y) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq924772 eq35
    | exact resolve eq35 eq924772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924772
  have eq926726 : (σ y) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq926080
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq926080
    | exact resolve eq926080 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926080
  have eq926747 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq926726
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq926726
    | exact resolve eq926726 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926726
  have eq926841 : (k (σ (M.op x y)) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq926747 eq471447
    | exact resolve eq471447 eq926747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471447
  have eq926843 : (k (σ (M.op x y)) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq926747 eq473119
    | exact resolve eq473119 eq926747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473119
  have eq927021 : (σ (σ y)) = (k (σ (σ x)) (σ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq926747 eq15
    | exact resolve eq15 eq926747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927248 : (k (σ (M.op x y)) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq926843
  have eq927250 : (k (σ (M.op x y)) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq926841
  have eq927714 : ∀ X0 : G, (k (σ y) X0) = (τ (k (k (σ (σ x)) (σ (σ x))) (σ X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq927021 eq46
    | exact resolve eq46 eq927021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq927021
  have eq927776 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ x) (σ x)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq927714 x
       have i₂ := eq48 sF4 sF4 x
       grind)
    | exact superpose eq48 eq927714
    | exact resolve eq927714 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq927714
  have eq928359 : (k (σ y) (k (σ y) (σ y))) = (k (k (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq927248 eq471673
    | exact resolve eq471673 eq927248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471673 eq927248
  have eq928466 : (k (σ y) (k (σ y) (σ y))) = (k (k (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq928359
  have eq934380 : (k (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq928466 eq927776
    | exact resolve eq927776 eq928466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927776 eq928466
  have eq934387 : (k (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq934380
  have eq934419 : (k (σ x) (σ x)) = (k (σ y) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq459191 eq934387
    | exact resolve eq934387 eq459191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459191 eq934387
  have eq934513 : (k (σ x) (σ x)) = (k (σ y) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq934419
  have eq934522 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq926747 eq934513
    | exact resolve eq934513 eq926747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926747 eq934513
  have eq934594 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq934522
  have eq934836 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq934594 eq121
    | exact resolve eq121 eq934594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934594
  have eq936286 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq900858 eq15
    | exact resolve eq15 eq900858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900858
  have eq936465 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq936286
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq936286
    | exact resolve eq936286 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936286
  have eq936519 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq936465
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq936465
    | exact resolve eq936465 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936465
  have eq937095 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq934836 eq459312
    | exact resolve eq459312 eq934836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459312
  have eq937185 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq934836 eq255
    | (have j0 := eq255 (τ (σ y)) X0
       grind)
    | (have r₁ := eq255 (τ (σ y)) x
       have r₂ := eq934836
       grind)
    | exact resolve eq255 eq934836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937226 : ∀ X0 : G, (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq937185 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937185
  have eq937315 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq937095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937095
  have eq937922 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq937315 eq934836
    | exact resolve eq934836 eq937315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934836
  have eq939231 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq937922
  have eq940827 : (σ (τ (σ y))) = (k (σ (M.op x y)) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq939231 eq15
    | exact resolve eq15 eq939231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939231
  have eq940880 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq940827
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq940827
    | exact resolve eq940827 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940827
  have eq940881 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq940880
    | exact resolve eq940880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940880
  have eq941822 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq940881 eq927250
    | exact resolve eq927250 eq940881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927250 eq940881
  have eq942045 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq941822
  have eq942096 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq942045 eq75
    | exact resolve eq75 eq942045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq942045
  have eq944838 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq942096 eq937315
    | exact resolve eq937315 eq942096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937315 eq942096
  have eq944925 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq944838
  have eq945442 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq944925 eq35
    | exact resolve eq35 eq944925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944925
  have eq945683 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq945442
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq945442
    | exact resolve eq945442 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945442
  have eq945740 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq945683
    | exact resolve eq945683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945683
  have eq967358 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq937226 eq42
    | exact resolve eq42 eq937226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq937226
  have eq967587 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq967358 eq15
    | exact resolve eq15 eq967358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967358
  have eq967630 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq967587
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq967587
    | exact resolve eq967587 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967587
  have eq967631 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq967630
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq967630
    | exact resolve eq967630 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967630
  have eq967632 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq967631
    | exact resolve eq967631 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967631
  have eq967633 : (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq967632
  have eq967803 : (M.op x y) = (τ (k (σ y) (σ x))) := by
    first
    | exact superpose eq967633 eq36
    | exact resolve eq36 eq967633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq968350 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq967803
       have i₂ := eq121 sF4 sF5
       grind)
    | exact superpose eq121 eq967803
    | exact resolve eq967803 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967803
  have eq968614 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq968350 eq15
    | exact resolve eq15 eq968350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968634 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) := by
    first
    | (have i₁ := eq968614
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq968614
    | exact resolve eq968614 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968614
  have eq968635 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq968634
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq968634
    | exact resolve eq968634 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968634
  have eq1312499 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq936519 eq15
    | exact resolve eq15 eq936519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936519
  have eq1312619 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1312499
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1312499
    | exact resolve eq1312499 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312499
  have eq1312638 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1312619
    | exact resolve eq1312619 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312619
  have eq1312649 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq1312638
       have r₂ := eq38215
       grind)
    | exact resolve eq1312638 eq38215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38215 eq1312638
  have eq1312655 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq1312649
       have r₂ := eq134154
       grind)
    | exact resolve eq1312649 eq134154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134154 eq1312649
  have eq1312660 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq967633 eq1312655
    | exact resolve eq1312655 eq967633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312655
  have eq1313491 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1312660 eq121
    | exact resolve eq121 eq1312660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1313531 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq1312660
  have eq1313624 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1313491
       have i₂ := eq121 sF4 sF5
       grind)
    | exact superpose eq121 eq1313491
    | exact resolve eq1313491 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1313491
  have eq1313638 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq968350 eq1313624
    | exact resolve eq1313624 eq968350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313624
  have eq1313831 : (M.op x y) ≠ (M.op x y) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1313638 eq572
    | (have r₁ := eq572
       have r₂ := eq1313638
       grind)
    | exact resolve eq572 eq1313638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1313638
  have eq1314295 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by grind
  clear eq1313831
  have eq1314350 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq968350 eq1314295
    | exact resolve eq1314295 eq968350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968350 eq1314295
  have eq1315369 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1314350 eq15
    | exact resolve eq15 eq1314350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314350
  have eq1315509 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1315369
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1315369
    | exact resolve eq1315369 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315369
  have eq1315511 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1315509
    | exact resolve eq1315509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315509
  have eq1315513 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq1315511
       have r₂ := eq522906
       grind)
    | exact resolve eq1315511 eq522906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522906 eq1315511
  have eq1318588 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq1315513 eq255
    | (have j0 := eq255 (σ y) X0
       grind)
    | (have r₁ := eq255 (σ y) x
       have r₂ := eq1315513
       grind)
    | exact resolve eq255 eq1315513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315513
  have eq1318643 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have j0 := eq1318588 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318588
  have eq1318658 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1318643 eq32
    | (have j1 := eq1318643 (σ x)
       grind)
    | exact resolve eq32 eq1318643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318643
  have eq1320561 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1318658 eq33
    | exact resolve eq33 eq1318658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318658
  have eq1320582 : (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq1320561
       have r₂ := eq967633
       grind)
    | exact resolve eq1320561 eq967633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967633 eq1320561
  have eq1321462 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1320582 eq35
    | exact resolve eq35 eq1320582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1320582
  have eq1323031 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1321462 eq968635
    | exact resolve eq968635 eq1321462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968635
  have eq1323032 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1321462 eq26
    | exact resolve eq26 eq1321462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1321462
  have eq1325571 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1323032 eq945740
    | exact resolve eq945740 eq1323032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945740
  have eq1325767 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq1325571
       have r₂ := eq1313531
       grind)
    | exact resolve eq1325571 eq1313531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313531 eq1325571
  have eq1328887 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1325767 eq255
    | (have j0 := eq255 (σ y) X0
       grind)
    | (have r₁ := eq255 (σ y) x
       have r₂ := eq1325767
       grind)
    | exact resolve eq255 eq1325767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq1325767
  have eq1328935 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1328887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328887
  have eq1332253 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1328935 eq32
    | (have j1 := eq1328935 (σ x)
       grind)
    | exact resolve eq32 eq1328935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1328935
  have eq1332256 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1323031 eq1332253
    | exact resolve eq1332253 eq1323031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323031 eq1332253
  have eq1332811 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1332256 eq33
    | exact resolve eq33 eq1332256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1332256
  have eq1332851 : False := by grind
  exact eq1332851

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then Y else if m(Y,X) = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyx_x_pyx_y_pyx_y_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq23 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (σ X0) (σ X1))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq24
    | exact resolve eq24 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq24
    | exact resolve eq24 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
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
  have eq76 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq91 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq52
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
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
  have eq152 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq76
    | exact resolve eq76 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq76
    | exact resolve eq76 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq182 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq91
    | exact resolve eq91 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq226 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
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
  have eq240 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq152
    | exact resolve eq152 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq271 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq160 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq160
    | exact resolve eq160 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq341 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq182
    | exact resolve eq182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq505 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq226
    | exact resolve eq226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq552 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq240 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq240
    | exact resolve eq240 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq240
    | exact resolve eq240 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq590 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq271
    | exact resolve eq271 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq682 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq341 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq341
    | exact resolve eq341 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq834 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq505 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq505
    | exact resolve eq505 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq856 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq552 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq552
    | exact resolve eq552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq919 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq568 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq568
    | exact resolve eq568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq986 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq590 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq590
    | exact resolve eq590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq1345 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq682 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq682
    | exact resolve eq682 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq2025 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq834 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq834
    | exact resolve eq834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq2120 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq856 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq856
    | exact resolve eq856 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq2222 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq919 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq919
    | exact resolve eq919 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq2260 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2261 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq2264 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2265 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2266 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq2266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2270 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq2261 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq2271 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2260
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq2260
    | exact resolve eq2260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2272 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq11 (σ y) (σ x)
       grind)
    | exact superpose eq11 eq2271
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq2271
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq2271 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2273 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2272
  have eq2280 : y ≠ y ∨ x = (M.op y y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2273
       grind)
    | exact superpose eq2273 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2273
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2273
       grind)
    | exact resolve eq13 eq2273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2281 : x ≠ y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2273
  have eq2282 : y ≠ y ∨ x = (M.op y y) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2280
  have eq2283 : x = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2282
  have eq2285 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq986 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq986
    | exact resolve eq986 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq2426 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq2283
       grind)
    | exact superpose eq2283 eq10
    | exact resolve eq10 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq2499 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2426
       grind)
    | exact superpose eq2426 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2426
       grind)
    | exact resolve eq13 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2501 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2499
  have eq2502 : x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2501
  have eq2576 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    grind
  have eq2578 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq2270 eq2576
    | (have j0 := eq2576 X0
       have j1 := eq2270 X0
       grind)
    | exact resolve eq2576 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270 eq2576
  have eq2582 : x ≠ x ∨ x = y ∨ x = (M.op y y) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2502
       grind)
    | exact superpose eq2502 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2502
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2502
       grind)
    | exact resolve eq12 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2585 : x ≠ x ∨ x = y ∨ x = (M.op y y) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2582
  have eq2586 : y = (k y x) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2585
  have eq2691 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1345 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1345
    | exact resolve eq1345 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq2732 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq2586
       grind)
    | exact superpose eq2586 eq10
    | exact resolve eq10 eq2586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586
  have eq2878 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2732
       grind)
    | exact superpose eq2732 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2732
       grind)
    | exact resolve eq12 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2879 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2732
       grind)
    | exact superpose eq2732 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq2880 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq2879
  have eq2881 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2878
  have eq2882 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2881
  have eq2886 : x = (M.op y y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2882
       have r₂ := eq2880
       grind)
    | exact resolve eq2882 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880 eq2882
  have eq2963 : x = (k y y) ∨ x = y ∨ x = y ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq2886
       grind)
    | exact superpose eq2886 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2886
  have eq2968 : x = (k y y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2963
  have eq3049 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2968
       grind)
    | exact superpose eq2968 eq10
    | exact resolve eq10 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968
  have eq3140 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq2264 X1 X0
       grind)
    | exact superpose eq2264 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq2264 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq2264 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq2264 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq2264 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3142 : (σ y) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq2264 (σ x) (σ y)
       grind)
    | exact superpose eq2264 eq2271
    | (have j1 := eq2264 x y
       grind)
    | exact resolve eq2271 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq3153 : (σ y) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3142
  have eq3155 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3140
  have eq3156 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3155 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155
  have eq3161 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2502 eq3153
    | exact resolve eq3153 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502 eq3153
  have eq3309 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3049
       have i₂ := eq11 (σ y) (σ y)
       grind)
    | exact superpose eq11 eq3049
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq3049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3314 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  have eq3316 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11 (σ y) (σ y)
       have i₂ := eq3049
       grind)
    | exact superpose eq3049 eq11
    | exact resolve eq11 eq3049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3320 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3316
  have eq3322 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3309
  have eq3324 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3320 eq3314
    | exact resolve eq3314 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314
  have eq3325 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq3320 eq3322
    | exact resolve eq3322 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322
  have eq3360 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2025 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2025
    | exact resolve eq2025 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq3398 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq3320
       grind)
    | exact superpose eq3320 eq9
    | exact resolve eq9 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3399 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq3320
       grind)
    | exact superpose eq3320 eq2271
    | exact resolve eq2271 eq3320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq3422 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3399
  have eq3423 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2120 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2120
    | exact resolve eq2120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq3824 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2222 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2222
    | exact resolve eq2222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq3963 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3325
       have i₂ := eq3324
       grind)
    | exact superpose eq3324 eq3325
    | exact resolve eq3325 eq3324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324 eq3325
  have eq3973 : x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq3963
  have eq3976 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2285 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2285
    | exact resolve eq2285 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285
  have eq4260 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3161
       have i₂ := eq3973
       grind)
    | exact superpose eq3973 eq3161
    | exact resolve eq3161 eq3973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq4261 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq4260
  have eq4262 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq4261
  have eq5776 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2691 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2691
    | exact resolve eq2691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2691
  have eq7708 : (σ x) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3422
       have i₂ := eq2267 (σ x)
       grind)
    | exact superpose eq2267 eq3422
    | (have j1 := eq2267 x
       grind)
    | exact resolve eq3422 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq7709 : (σ x) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq7708
  have eq8079 : (M.op x x) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  have eq8083 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq4262 eq8079
    | exact resolve eq8079 eq4262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4262 eq8079
  have eq8456 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq8083
       grind)
    | exact superpose eq8083 eq10
    | exact resolve eq10 eq8083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8083
  have eq8457 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq8456
  have eq8656 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  have eq8661 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq8457 eq8656
    | exact resolve eq8656 eq8457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8457 eq8656
  have eq8662 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq8661
  have eq8917 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq8662
       grind)
    | exact superpose eq8662 eq10
    | exact resolve eq10 eq8662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8918 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  have eq9015 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3360 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3360
    | exact resolve eq3360 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9216 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3423 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3423
    | exact resolve eq3423 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3423
  have eq9514 : (k y y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq8917
       grind)
    | exact superpose eq8917 eq18
    | exact resolve eq18 eq8917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9579 : (σ x) = (k (σ x) (σ x)) ∨ (σ (σ x)) = (k (σ (σ y)) (σ (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq10 (σ y) (σ y)
       have i₂ := eq8917
       grind)
    | exact superpose eq8917 eq10
    | exact resolve eq10 eq8917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9645 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq9514
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq9514
    | exact resolve eq9514 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9514
  have eq10077 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3824 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3824
    | exact resolve eq3824 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq10216 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3976 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3976
    | exact resolve eq3976 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq10515 : (σ (σ x)) = (k (σ (σ x)) (σ (σ x))) ∨ (σ (σ x)) = (k (σ (σ y)) (σ (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq10 (σ x) (σ x)
       have i₂ := eq9579
       grind)
    | exact superpose eq9579 eq10
    | exact resolve eq10 eq9579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9579
  have eq10589 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq8662
       have r₂ := eq7709
       grind)
    | exact resolve eq8662 eq7709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7709
  have eq10731 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3398
       have i₂ := eq10589
       grind)
    | exact superpose eq10589 eq3398
    | exact resolve eq3398 eq10589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398 eq10589
  have eq10733 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq10731
  have eq11340 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10733
       have i₂ := eq2267 (σ x)
       grind)
    | exact superpose eq2267 eq10733
    | (have j1 := eq2267 (σ x)
       grind)
    | (have r₁ := eq10733
       have r₂ := eq2267 (σ x)
       grind)
    | exact resolve eq10733 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267 eq10733
  have eq11341 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by grind
  clear eq11340
  have eq11351 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq11341
       have r₂ := eq8662
       grind)
    | exact resolve eq11341 eq8662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8662 eq11341
  have eq11555 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3360 x (σ y)
       have i₂ := eq11351
       grind)
    | exact superpose eq11351 eq3360
    | exact resolve eq3360 eq11351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360 eq11351
  have eq11560 : y = (k y x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11555
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq11555
    | exact resolve eq11555 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11555
  have eq12484 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5776 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq5776
    | exact resolve eq5776 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5776
  have eq12579 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq2578 (σ y)
       have i₂ := eq8917
       grind)
    | exact superpose eq8917 eq2578
    | (have j0 := eq2578 (σ x)
       grind)
    | exact resolve eq2578 eq8917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8917
  have eq12626 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq2578 y
       have i₂ := eq9645
       grind)
    | exact superpose eq9645 eq2578
    | (have j0 := eq2578 (σ x)
       grind)
    | exact resolve eq2578 eq9645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9645
  have eq12689 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq9
       have i₂ := eq12626
       grind)
    | exact superpose eq12626 eq9
    | exact resolve eq9 eq12626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12626
  have eq12704 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq12689
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq12689
    | exact resolve eq12689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12689
  have eq15104 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq12704
       have i₂ := eq12579
       grind)
    | exact superpose eq12579 eq12704
    | (have r₁ := eq12704
       have r₂ := eq12579
       grind)
    | exact resolve eq12704 eq12579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12579 eq12704
  have eq15111 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ x) = (σ y) := by grind
  clear eq15104
  have eq15112 : x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ x) = (σ y) := by grind
  clear eq15111
  have eq15149 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8918
       have i₂ := eq15112
       grind)
    | exact superpose eq15112 eq8918
    | (have r₁ := eq8918
       have r₂ := eq15112
       grind)
    | exact resolve eq8918 eq15112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8918 eq15112
  have eq15165 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ x) = (σ y) := by grind
  clear eq15149
  have eq15166 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ x) = (σ y) := by grind
  clear eq15165
  have eq15628 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9015 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq9015
    | exact resolve eq9015 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9015
  have eq15798 : (τ (σ (σ x))) = (k (σ x) (τ (σ (σ x)))) ∨ (σ (σ x)) = (k (σ (σ y)) (σ (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq9216 (σ x) (σ (σ x))
       have i₂ := eq10515
       grind)
    | exact superpose eq10515 eq9216
    | exact resolve eq9216 eq10515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9216 eq10515
  have eq16053 : (σ x) = (k (σ x) (σ x)) ∨ (σ (σ x)) = (k (σ (σ y)) (σ (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) := by
    first
    | (have i₁ := eq15798
       have i₂ := eq16 (σ x)
       grind)
    | exact superpose eq16 eq15798
    | exact resolve eq15798 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15798
  have eq16063 : (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ (σ x)) = (k (σ (σ x)) (σ (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq15166 eq16053
    | exact resolve eq16053 eq15166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15166 eq16053
  have eq18392 : (τ (σ (σ y))) = (k (τ (σ (σ y))) (σ x)) ∨ (σ (σ x)) = (k (σ (σ x)) (σ (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10077 (σ x) (σ (σ y))
       have i₂ := eq16063
       grind)
    | exact superpose eq16063 eq10077
    | exact resolve eq10077 eq16063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16063
  have eq18399 : (σ (σ x)) = (k (σ (σ x)) (σ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18392
       have i₂ := eq16 (σ y)
       grind)
    | exact superpose eq16 eq18392
    | exact resolve eq18392 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18392
  have eq18886 : (τ (σ (σ x))) = (k (τ (σ (σ x))) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10077 (σ x) (σ (σ x))
       have i₂ := eq18399
       grind)
    | exact superpose eq18399 eq10077
    | exact resolve eq10077 eq18399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10077 eq18399
  have eq18892 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18886
       have i₂ := eq16 (σ x)
       grind)
    | exact superpose eq16 eq18886
    | exact resolve eq18886 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18886
  have eq18893 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq18892
  have eq19421 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10216 x (σ y)
       have i₂ := eq18893
       grind)
    | exact superpose eq18893 eq10216
    | exact resolve eq10216 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10216
  have eq19425 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  have eq19429 : y = (k y x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19421
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq19421
    | exact resolve eq19421 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19421
  have eq19578 : y ≠ (k y x) ∨ x = (k y x) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq3156 y x
       grind)
    | exact superpose eq3156 eq9
    | (have j1 := eq3156 y x
       grind)
    | exact resolve eq9 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19959 : y ≠ y ∨ x = y ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19578
       have i₂ := eq11560
       grind)
    | exact superpose eq11560 eq19578
    | (have r₁ := eq19578
       have r₂ := eq11560
       grind)
    | exact resolve eq19578 eq11560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11560
  have eq19960 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq19959
  have eq20287 : y ≠ y ∨ x = y ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19578
       have i₂ := eq19429
       grind)
    | exact superpose eq19429 eq19578
    | (have r₁ := eq19578
       have r₂ := eq19429
       grind)
    | exact resolve eq19578 eq19429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19578
  have eq20291 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq20287
  have eq24742 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq20291
       have i₂ := eq3156 (σ y) (σ x)
       grind)
    | exact superpose eq3156 eq20291
    | (have j1 := eq3156 (σ y) (σ x)
       grind)
    | (have r₁ := eq20291
       have r₂ := eq3156 (σ y) (σ x)
       grind)
    | (have r₁ := eq20291
       have r₂ := eq3156 (σ x) (σ x)
       grind)
    | exact resolve eq20291 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20291
  have eq24745 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq24742
  have eq24746 : x = y ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq24745
  have eq24756 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq24746
       have r₂ := eq18893
       grind)
    | exact resolve eq24746 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24746
  have eq25234 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11 (σ y) (σ y)
       have i₂ := eq24756
       grind)
    | exact superpose eq24756 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq24756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24756
  have eq25238 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq25234
  have eq25243 : x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq25238
       have r₂ := eq19425
       grind)
    | exact resolve eq25238 eq19425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25238
  have eq25985 : x = (k y y) ∨ x = y ∨ x = y ∨ x = y ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq25243
       grind)
    | exact superpose eq25243 eq11
    | exact resolve eq11 eq25243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25243
  have eq25990 : x = (k y y) ∨ x = y ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq25985
  have eq26763 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq25990
       grind)
    | exact superpose eq25990 eq10
    | exact resolve eq10 eq25990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25990
  have eq26764 : x = y ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq26763
  have eq27143 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq19425
       have i₂ := eq26764
       grind)
    | exact superpose eq26764 eq19425
    | exact resolve eq19425 eq26764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26764
  have eq27149 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq27143
  have eq27150 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq27149
  have eq27552 : (k y y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq27150
       grind)
    | exact superpose eq27150 eq18
    | exact resolve eq18 eq27150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27644 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2578 (σ y)
       have i₂ := eq27150
       grind)
    | exact superpose eq27150 eq2578
    | (have j0 := eq2578 (σ x)
       grind)
    | exact resolve eq2578 eq27150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27653 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq18893 eq27644
    | exact resolve eq27644 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27644
  have eq27745 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq27552
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq27552
    | exact resolve eq27552 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27552
  have eq27749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq27653
       have r₂ := eq19425
       grind)
    | exact resolve eq27653 eq19425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27653
  have eq28204 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2578 y
       have i₂ := eq27745
       grind)
    | exact superpose eq27745 eq2578
    | (have j0 := eq2578 (σ x)
       grind)
    | exact resolve eq2578 eq27745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27745
  have eq28213 : y = (M.op x y) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq19429 eq28204
    | exact resolve eq28204 eq19429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19429 eq28204
  have eq28596 : (σ y) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq27749
       grind)
    | exact superpose eq27749 eq2271
    | exact resolve eq2271 eq27749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28640 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq28596
       have r₂ := eq18893
       grind)
    | exact resolve eq28596 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18893 eq28596
  have eq28645 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq28213 eq28640
    | exact resolve eq28640 eq28213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28640
  have eq28646 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq28213 eq28645
    | exact resolve eq28645 eq28213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28645
  have eq28647 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq28646
  have eq29405 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq28213
       grind)
    | exact superpose eq28213 eq9
    | exact resolve eq9 eq28213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28213
  have eq29427 : x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq29405
       have r₂ := eq27749
       grind)
    | exact resolve eq29405 eq27749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27749 eq29405
  have eq29458 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq27150
       have i₂ := eq29427
       grind)
    | exact superpose eq29427 eq27150
    | exact resolve eq27150 eq29427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29427
  have eq29466 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq29458
  have eq29602 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12484 x (σ x)
       have i₂ := eq29466
       grind)
    | exact superpose eq29466 eq12484
    | exact resolve eq12484 eq29466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12484
  have eq29603 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2265 (σ x) (σ x)
       have i₂ := eq29466
       grind)
    | exact superpose eq29466 eq2265
    | (have j0 := eq2265 (σ x) (σ x)
       grind)
    | (have r₁ := eq2265 (σ x) (σ x)
       have r₂ := eq29466
       grind)
    | (have r₁ := eq2265 (σ x) (σ y)
       have r₂ := eq29466
       grind)
    | exact resolve eq2265 eq29466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29466
  have eq29606 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq29603
  have eq29607 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq29606
  have eq29611 : x = (k x x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq29602
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq29602
    | exact resolve eq29602 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29602
  have eq29713 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2265 x x
       have i₂ := eq29611
       grind)
    | exact superpose eq29611 eq2265
    | (have j0 := eq2265 x x
       grind)
    | (have r₁ := eq2265 x x
       have r₂ := eq29611
       grind)
    | (have r₁ := eq2265 (σ x) (σ y)
       have r₂ := eq29611
       grind)
    | exact resolve eq2265 eq29611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29611
  have eq29716 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq29713
  have eq29717 : x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq29716
  have eq45511 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19960
       have i₂ := eq3156 (σ y) (σ x)
       grind)
    | exact superpose eq3156 eq19960
    | (have j1 := eq3156 (σ y) (σ x)
       grind)
    | (have r₁ := eq19960
       have r₂ := eq3156 (σ y) (σ x)
       grind)
    | exact resolve eq19960 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156 eq19960
  have eq45514 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq45511
  have eq45515 : x = y ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq45514
  have eq45525 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq45515
       have r₂ := eq3049
       grind)
    | exact resolve eq45515 eq3049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049 eq45515
  have eq45995 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11 (σ y) (σ y)
       have i₂ := eq45525
       grind)
    | exact superpose eq45525 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq45525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45525
  have eq46000 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq45995
  have eq46944 : x = (k y y) ∨ x = y ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq46000
       grind)
    | exact superpose eq46000 eq11
    | exact resolve eq11 eq46000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46000
  have eq46949 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq46944
  have eq47432 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq46949
       grind)
    | exact superpose eq46949 eq10
    | exact resolve eq10 eq46949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46949
  have eq47433 : x = y ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq47432
  have eq47714 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq47433
       grind)
    | exact superpose eq47433 eq9
    | exact resolve eq9 eq47433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47433
  have eq47796 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq29607 eq47714
    | exact resolve eq47714 eq29607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47714
  have eq47797 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq29717 eq47796
    | exact resolve eq47796 eq29717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47796
  have eq47798 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq47797
  have eq48075 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq47798
       grind)
    | exact superpose eq47798 eq18
    | exact resolve eq18 eq47798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48208 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2578 (σ y)
       have i₂ := eq47798
       grind)
    | exact superpose eq47798 eq2578
    | exact resolve eq2578 eq47798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47798
  have eq48213 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq48208
  have eq48346 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq48075
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq48075
    | exact resolve eq48075 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48075
  have eq48473 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2578 y
       have i₂ := eq48346
       grind)
    | exact superpose eq48346 eq2578
    | exact resolve eq2578 eq48346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48346
  have eq49773 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq48473
       grind)
    | exact superpose eq48473 eq9
    | exact resolve eq9 eq48473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48473
  have eq49803 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq49773
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq49773
    | exact resolve eq49773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49773
  have eq49808 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq49803
       have r₂ := eq48213
       grind)
    | exact resolve eq49803 eq48213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48213 eq49803
  have eq49809 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq49808
       grind)
    | exact superpose eq49808 eq9
    | exact resolve eq9 eq49808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49891 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq29607 eq49809
    | exact resolve eq49809 eq29607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29607 eq49809
  have eq49892 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq29717 eq49891
    | exact resolve eq49891 eq29717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29717 eq49891
  have eq49893 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq49892
  have eq49982 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15628 y (σ x)
       have i₂ := eq49893
       grind)
    | exact superpose eq49893 eq15628
    | exact resolve eq15628 eq49893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15628
  have eq50046 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2265 (σ x) (σ y)
       have i₂ := eq49893
       grind)
    | exact superpose eq49893 eq2265
    | (have j0 := eq2265 (σ x) (σ y)
       grind)
    | (have r₁ := eq2265 (σ x) (σ y)
       have r₂ := eq49893
       grind)
    | exact resolve eq2265 eq49893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50049 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq50046
  have eq50116 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49982
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq49982
    | exact resolve eq49982 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49982
  have eq50261 : x ≠ x ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2265 x y
       have i₂ := eq50116
       grind)
    | exact superpose eq50116 eq2265
    | (have j0 := eq2265 x y
       grind)
    | (have r₁ := eq2265 x y
       have r₂ := eq50116
       grind)
    | exact resolve eq2265 eq50116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50264 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq50261
  have eq51243 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq50264
  have eq51256 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq50116 eq51243
    | exact resolve eq51243 eq50116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51243
  have eq51257 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq51256
  have eq51269 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq51257
       grind)
    | exact superpose eq51257 eq9
    | exact resolve eq9 eq51257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51277 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq51257
  have eq56531 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq50049
  have eq56550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq49893 eq56531
    | exact resolve eq56531 eq49893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56531
  have eq56551 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq56550
  have eq56860 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq51269
       have i₂ := eq56551
       grind)
    | exact superpose eq56551 eq51269
    | (have r₁ := eq51269
       have r₂ := eq56551
       grind)
    | exact resolve eq51269 eq56551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51269 eq56551
  have eq56866 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56860
  have eq56867 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56866
  have eq56918 : x ≠ x ∨ x = y ∨ x = (M.op y y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq56867
       grind)
    | exact superpose eq56867 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq56867
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq56867
       grind)
    | exact resolve eq12 eq56867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56867
  have eq56920 : x = y ∨ x = (M.op y y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56918
  have eq56934 : x = y ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50116 eq56920
    | exact resolve eq56920 eq50116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56920
  have eq56935 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56934
  have eq56947 : x = (k y y) ∨ x = y ∨ x = y ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq56935
       grind)
    | exact superpose eq56935 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq56935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56935
  have eq56952 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56947
  have eq57256 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq56952
       grind)
    | exact superpose eq56952 eq10
    | exact resolve eq10 eq56952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56952
  have eq57562 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq57256
       grind)
    | exact superpose eq57256 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq57256
       grind)
    | exact resolve eq12 eq57256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57256
  have eq57564 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57562
  have eq57565 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57564
  have eq57588 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq49808 eq57565
    | exact resolve eq57565 eq49808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49808 eq57565
  have eq57589 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57588
  have eq57881 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq11 (σ y) (σ y)
       have i₂ := eq57589
       grind)
    | exact superpose eq57589 eq11
    | exact resolve eq11 eq57589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57589
  have eq57886 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57881
  have eq57899 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq57886
       grind)
    | exact superpose eq57886 eq9
    | exact resolve eq9 eq57886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57900 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq57886
       grind)
    | exact superpose eq57886 eq2271
    | exact resolve eq2271 eq57886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57909 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3161
       have i₂ := eq57886
       grind)
    | exact superpose eq57886 eq3161
    | (have r₁ := eq3161
       have r₂ := eq57886
       grind)
    | exact resolve eq3161 eq57886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161
  have eq57929 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq27150
       have i₂ := eq57886
       grind)
    | exact superpose eq57886 eq27150
    | exact resolve eq27150 eq57886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27150
  have eq57935 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq28647
       have i₂ := eq57886
       grind)
    | exact superpose eq57886 eq28647
    | exact resolve eq28647 eq57886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28647 eq57886
  have eq57936 : x = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57935
  have eq57943 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57929
  have eq57967 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57909
  have eq57968 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57967
  have eq57980 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq57900
  have eq57981 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq57936 eq57980
    | exact resolve eq57980 eq57936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57936 eq57980
  have eq57982 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq57981
       have r₂ := eq57968
       grind)
    | exact resolve eq57981 eq57968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57968 eq57981
  have eq58145 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2265 (σ x) (σ x)
       have i₂ := eq57943
       grind)
    | exact superpose eq57943 eq2265
    | (have j0 := eq2265 (σ x) (σ x)
       grind)
    | (have r₁ := eq2265 (σ x) (σ x)
       have r₂ := eq57943
       grind)
    | exact resolve eq2265 eq57943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57943
  have eq58148 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq58145
  have eq58149 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq58148
  have eq59161 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq57899
       have i₂ := eq57982
       grind)
    | exact superpose eq57982 eq57899
    | exact resolve eq57899 eq57982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57899 eq57982
  have eq59169 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq59161
  have eq59178 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq59169
       have r₂ := eq58149
       grind)
    | exact resolve eq59169 eq58149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58149 eq59169
  have eq59197 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq59178
       grind)
    | exact superpose eq59178 eq18
    | exact resolve eq18 eq59178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq59332 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2578 (σ y)
       have i₂ := eq59178
       grind)
    | exact superpose eq59178 eq2578
    | exact resolve eq2578 eq59178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59178
  have eq59337 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq59332
  have eq59338 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq49893 eq59337
    | exact resolve eq59337 eq49893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49893 eq59337
  have eq59473 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq59197
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq59197
    | exact resolve eq59197 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59197
  have eq59600 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2578 y
       have i₂ := eq59473
       grind)
    | exact superpose eq59473 eq2578
    | exact resolve eq2578 eq59473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578 eq59473
  have eq59605 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq50116 eq59600
    | exact resolve eq59600 eq50116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50116 eq59600
  have eq59686 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq59605
       have r₂ := eq51277
       grind)
    | exact resolve eq59605 eq51277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51277 eq59605
  have eq59702 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq59686
       grind)
    | exact superpose eq59686 eq9
    | exact resolve eq9 eq59686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59686
  have eq59728 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq59702
       have r₂ := eq59338
       grind)
    | exact resolve eq59702 eq59338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59338 eq59702
  have eq59736 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq19425
       have r₂ := eq59728
       grind)
    | exact resolve eq19425 eq59728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19425
  have eq59744 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq59736
       have i₂ := eq59728
       grind)
    | exact superpose eq59728 eq59736
    | exact resolve eq59736 eq59728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59736
  have eq59745 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq59744
  have eq59756 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq59728
       grind)
    | exact superpose eq59728 eq2271
    | exact resolve eq2271 eq59728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq59784 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq59728
       grind)
    | exact superpose eq59728 eq16
    | exact resolve eq16 eq59728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60103 : x = y := by
    first
    | (have i₁ := eq59784
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq59784
    | exact resolve eq59784 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59784
  have eq60108 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq59756
       have i₂ := eq59745
       grind)
    | exact superpose eq59745 eq59756
    | exact resolve eq59756 eq59745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59745 eq59756
  have eq60109 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq2281
       have r₂ := eq60103
       grind)
    | exact resolve eq2281 eq60103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq60120 : x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq60108
       have i₂ := eq60103
       grind)
    | exact superpose eq60103 eq60108
    | exact resolve eq60108 eq60103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60108
  have eq60121 : x = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq60109
       have i₂ := eq60103
       grind)
    | exact superpose eq60103 eq60109
    | exact resolve eq60109 eq60103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60109
  have eq60132 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq60120
       have i₂ := eq60103
       grind)
    | exact superpose eq60103 eq60120
    | exact resolve eq60120 eq60103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60120
  have eq60133 : x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq60132
  have eq60134 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq60121
       have i₂ := eq60103
       grind)
    | exact superpose eq60103 eq60121
    | exact resolve eq60121 eq60103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60121
  have eq60135 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq60134
  have eq60144 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60133
       have i₂ := eq60103
       grind)
    | exact superpose eq60103 eq60133
    | exact resolve eq60133 eq60103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60133
  have eq60145 : x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq60144
  have eq60146 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq60135
       have i₂ := eq59728
       grind)
    | exact superpose eq59728 eq60135
    | exact resolve eq60135 eq59728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60135
  have eq60156 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq60146
       have i₂ := eq59728
       grind)
    | exact superpose eq59728 eq60146
    | exact resolve eq60146 eq59728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60146
  have eq60157 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq60156
  have eq60159 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq60157
       have i₂ := eq59728
       grind)
    | exact superpose eq59728 eq60157
    | exact resolve eq60157 eq59728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59728 eq60157
  have eq60160 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq60159
  have eq60161 : x = (M.op x x) := by
    first
    | (have r₁ := eq60160
       have r₂ := eq60145
       grind)
    | exact resolve eq60160 eq60145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60145 eq60160
  have eq60162 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq60103
       grind)
    | exact superpose eq60103 eq9
    | exact resolve eq9 eq60103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60103
  have eq60212 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60162
       have i₂ := eq60161
       grind)
    | exact superpose eq60161 eq60162
    | exact resolve eq60162 eq60161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60162
  have eq60238 : (M.op x x) = (k x x) := by grind
  have eq60240 : x = (k x x) := by
    first
    | (have i₁ := eq60238
       have i₂ := eq60161
       grind)
    | exact superpose eq60161 eq60238
    | exact resolve eq60238 eq60161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60161 eq60238
  have eq60245 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq23 x x
       have i₂ := eq60240
       grind)
    | exact superpose eq60240 eq23
    | exact resolve eq23 eq60240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq60240
  have eq60826 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2265 (σ x) (σ x)
       have i₂ := eq60245
       grind)
    | exact superpose eq60245 eq2265
    | (have j0 := eq2265 (σ x) (σ x)
       grind)
    | (have r₁ := eq2265 (σ x) (σ x)
       have r₂ := eq60245
       grind)
    | exact resolve eq2265 eq60245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265 eq60245
  have eq60829 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq60826
  have eq60830 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq60829
  have eq60831 : False := by grind
  exact eq60831

/-- `x □ y = if m(Y,X) = Y then Y else if m(X,Y) = Y then X else if m(Y,X) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pxy_y_pyx_x_y_x_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  clear eq24 eq38
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
  clear eq40 eq41
  have eq47 : (M.op x y) ≠ (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq11
    | (have j0 := eq11 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq11 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq53 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq52
    | exact resolve eq52 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (τ (k (k (σ X0) (σ X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (k X0 X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq52
    | exact resolve eq52 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (k X2 (k X0 X1)) = (τ (k (σ X2) (k (σ X0) (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (M.op x y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (M.op x y) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq42 eq12
    | (have j0 := eq12 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq62 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq62
    | exact resolve eq62 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (M.op x y) ≠ (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (τ (σ y)) (τ (σ x))) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq13
    | (have j0 := eq13 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq13 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq42 eq14
    | (have j0 := eq14 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq130 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq138 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq125 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq125 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq125 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq154 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq53
    | exact resolve eq53 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123 eq33
    | exact resolve eq33 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq412 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq416 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq121
       have i₂ := eq14 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq14 eq121
    | (have j1 := eq14 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq121 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq121 eq13
    | (have j0 := eq13 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq13 (τ (σ x)) (τ (σ y))
       have r₂ := eq121
       grind)
    | exact resolve eq13 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq121 eq12
    | (have j0 := eq12 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq12 (τ (σ y)) (τ (σ x))
       have r₂ := eq121
       grind)
    | exact resolve eq12 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq420 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq418
  have eq421 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq417
  have eq422 : (M.op x y) = (τ (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq42 eq420
    | exact resolve eq420 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq423 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq422
  have eq424 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq42 eq421
    | exact resolve eq421 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq425 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq424
  have eq426 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have r₁ := eq416
       have r₂ := eq78
       grind)
    | exact resolve eq416 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq427 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq42 eq425
    | exact resolve eq425 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq428 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have j1 := eq12 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq426
       have r₂ := eq12 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq426
       have r₂ := eq12 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq426 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq430 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq423 eq15
    | exact resolve eq15 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq432 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq430
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq430
    | exact resolve eq430 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq433 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq432
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq432
    | exact resolve eq432 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq439 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq433 eq15
    | exact resolve eq15 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq439
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq439
    | exact resolve eq439 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq442 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq441
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq441
    | exact resolve eq441 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq443 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq26 eq442
    | exact resolve eq442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq444 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq443 eq131
    | (have j0 := eq131 (σ x) (σ y)
       grind)
    | (have r₁ := eq131 (σ x) (σ y)
       have r₂ := eq443
       grind)
    | exact resolve eq131 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq443 eq154
    | exact resolve eq154 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq443 eq15
    | exact resolve eq15 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq444
  have eq448 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq447
    | exact resolve eq447 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq449 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq448
    | exact resolve eq448 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq450 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq449
       have r₂ := eq410
       grind)
    | exact resolve eq449 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq456 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq450
       have i₂ := eq14 sF4 sF5
       grind)
    | exact superpose eq14 eq450
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq450 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq450 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq450
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq450
       grind)
    | exact resolve eq13 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq450 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq450
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq450
       grind)
    | exact resolve eq12 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq450 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq450
       grind)
    | exact resolve eq11 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq458
  have eq461 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq457
  have eq462 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq460
    | exact resolve eq460 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq463 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq462
  have eq464 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq461
    | exact resolve eq461 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq465 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq464
  have eq466 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq456
       have r₂ := eq79
       grind)
    | exact resolve eq456 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq467 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq465
    | exact resolve eq465 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq468 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq466
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq466
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq466 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq471 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq463 eq154
    | exact resolve eq154 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq463 eq15
    | exact resolve eq15 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq445 eq131
    | (have j0 := eq131 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq131 (τ (σ x)) (τ (σ y))
       have r₂ := eq445
       grind)
    | exact resolve eq131 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq486
  have eq494 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq42 eq489
    | exact resolve eq489 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq495 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq494
  have eq500 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq495
    | exact resolve eq495 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq501 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq500
  have eq508 : ∀ X0 : G, (k (k (σ y) (σ x)) X0) = (τ (k (σ (σ y)) (σ X0))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq446 eq54
    | exact resolve eq54 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq527 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ x)) X0) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq508 x
       have i₂ := eq52 sF5 x
       grind)
    | exact superpose eq52 eq508
    | exact resolve eq508 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq538 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq501 eq13
    | (have j0 := eq13 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq13 (τ (σ x)) (τ (σ y))
       have r₂ := eq501
       grind)
    | exact resolve eq13 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq538
  have eq543 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq542
    | exact resolve eq542 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq544 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq543
  have eq545 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq544
    | exact resolve eq544 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq549 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123 eq467
    | exact resolve eq467 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq467 eq48
    | (have r₁ := eq48
       have r₂ := eq467
       grind)
    | exact resolve eq48 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq467 eq33
    | exact resolve eq33 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq557 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq553
       have r₂ := eq48
       grind)
    | exact resolve eq553 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq559 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq549
       have r₂ := eq48
       grind)
    | exact resolve eq549 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq588 : ∀ X0 : G, (k (σ y) (σ x)) ≠ (k (σ y) X0) ∨ (M.op (k (σ y) (σ x)) X0) = X0 ∨ (k (σ y) (σ x)) = (M.op X0 (k (σ y) (σ x))) ∨ (M.op X0 (k (σ y) (σ x))) = X0 ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq527 eq131
    | (have j0 := eq131 X0 (k (σ y) (σ x))
       grind)
    | (have r₁ := eq131 (σ x) (k (σ y) (σ x))
       have r₂ := eq527 (σ x)
       grind)
    | exact resolve eq131 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (τ (k (σ y) (σ x))) X0) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq527 eq53
    | exact resolve eq53 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq596 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (k (τ (σ y)) (τ (σ x))) X0) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq591 X0
       have i₂ := eq154 sF4 sF5
       grind)
    | exact superpose eq154 eq591
    | exact resolve eq591 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq601 : ∀ X0 : G, (k (τ (σ y)) X0) = (k (k (τ (σ y)) (τ (σ x))) X0) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq596 x
       have i₂ := eq53 sF5 x
       grind)
    | exact superpose eq53 eq596
    | exact resolve eq596 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq626 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq471 eq138
    | (have j0 := eq138 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq138 (τ (σ y)) (τ (σ x))
       have r₂ := eq471
       grind)
    | exact resolve eq138 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq626
  have eq640 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq632
       have r₂ := eq78
       grind)
    | exact resolve eq632 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq646 : (M.op x y) = (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq42 eq640
    | exact resolve eq640 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq647 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq646
  have eq651 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq427 eq471
    | exact resolve eq471 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq659 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq651
  have eq668 : ∀ X0 : G, (k (k (σ y) (σ x)) X0) = (τ (k (σ (σ y)) (σ X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq472 eq54
    | exact resolve eq54 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq687 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq668 x
       have i₂ := eq52 sF5 x
       grind)
    | exact superpose eq52 eq668
    | exact resolve eq668 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq696 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq428 eq11
    | (have j0 := eq11 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq11 (τ (σ x)) (τ (σ y))
       have r₂ := eq428
       grind)
    | exact resolve eq11 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq698 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) := by grind
  clear eq696
  have eq773 : ∀ X0 : G, (k (σ y) (σ x)) ≠ (k (σ y) X0) ∨ (M.op (k (σ y) (σ x)) X0) = X0 ∨ (k (σ y) (σ x)) = (M.op X0 (k (σ y) (σ x))) ∨ (M.op X0 (k (σ y) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq687 eq131
    | (have j0 := eq131 X0 (k (σ y) (σ x))
       grind)
    | (have r₁ := eq131 (σ x) (k (σ y) (σ x))
       have r₂ := eq687 (σ x)
       grind)
    | exact resolve eq131 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq880 : (σ (τ (σ y))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq698 eq15
    | exact resolve eq15 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq885 : (σ y) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq880
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq880
    | exact resolve eq880 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq889 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq885
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq885
    | exact resolve eq885 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq899 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq545 eq15
    | exact resolve eq15 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq899
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq899
    | exact resolve eq899 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq903 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq902
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq902
    | exact resolve eq902 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq904 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq903
    | exact resolve eq903 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq905 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq904 eq36
    | exact resolve eq36 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : (k (σ y) (σ x)) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  have eq926 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq905
       have i₂ := eq154 sF4 sF5
       grind)
    | exact superpose eq154 eq905
    | exact resolve eq905 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq984 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq889 eq15
    | exact resolve eq15 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq992 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq984
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq984
    | exact resolve eq984 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq996 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq992
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq992
    | exact resolve eq992 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1024 : ∀ X0 : G, (k (τ (σ y)) (τ (σ x))) ≠ (k (τ (σ y)) X0) ∨ (M.op (k (τ (σ y)) (τ (σ x))) X0) = X0 ∨ (k (τ (σ y)) (τ (σ x))) = (M.op X0 (k (τ (σ y)) (τ (σ x)))) ∨ (M.op X0 (k (τ (σ y)) (τ (σ x)))) = X0 ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq601 eq131
    | (have j0 := eq131 X0 (k (τ (σ y)) (τ (σ x)))
       grind)
    | (have r₁ := eq131 (τ (σ x)) (k (τ (σ y)) (τ (σ x)))
       have r₂ := eq601 (τ (σ x))
       grind)
    | exact resolve eq131 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq1297 : (σ y) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq463 eq915
    | exact resolve eq915 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1300 : (σ y) ≠ (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1297
  have eq1305 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq926 eq471
    | exact resolve eq471 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq1319 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1305
  have eq1330 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (k (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq1319 eq62
    | exact resolve eq62 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1337 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1319 eq554
    | (have r₁ := eq554
       have r₂ := eq1319
       grind)
    | exact resolve eq554 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq1319
  have eq1342 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1337
  have eq1343 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1342
  have eq1351 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (k (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1330 x
       have i₂ := eq58 (k sF4 sF5) x
       grind)
    | exact superpose eq58 eq1330
    | exact resolve eq1330 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq1330
  have eq1359 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (τ (σ x)) (τ (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1351 X0
       have i₂ := eq154 sF5 sF4
       grind)
    | exact superpose eq154 eq1351
    | exact resolve eq1351 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1362 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1343 eq42
    | exact resolve eq42 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1390 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1343 eq35
    | exact resolve eq35 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1390
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1390
    | exact resolve eq1390 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1422 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1421
  have eq1430 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1422 eq78
    | (have r₁ := eq78
       have r₂ := eq1422
       grind)
    | exact resolve eq78 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1431 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1422 eq97
    | (have r₁ := eq97
       have r₂ := eq1422
       grind)
    | exact resolve eq97 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1422 eq35
    | exact resolve eq35 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1445 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1431
  have eq1446 : (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1445
  have eq1447 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1430
  have eq1449 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1438
    | exact resolve eq1438 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1465 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1449 eq47
    | (have r₁ := eq47
       have r₂ := eq1449
       grind)
    | exact resolve eq47 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1466 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1449 eq35
    | exact resolve eq35 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1467 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1465
  have eq1468 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq1466
    | exact resolve eq1466 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1474 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1468 eq98
    | (have r₁ := eq98
       have r₂ := eq1468
       grind)
    | exact resolve eq98 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1476 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1474
  have eq1477 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1476
  have eq1486 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq996 eq12
    | (have j0 := eq12 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq12 (τ (σ y)) (τ (σ x))
       have r₂ := eq996
       grind)
    | exact resolve eq12 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1488 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq1486
  have eq1493 : (M.op x y) = (τ (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq42 eq1488
    | exact resolve eq1488 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1494 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq1493
  have eq1511 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1467 eq15
    | exact resolve eq15 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1515 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1511
    | exact resolve eq1511 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1516 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1515
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1515
    | exact resolve eq1515 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq1535 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1516 eq15
    | exact resolve eq15 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1568 : ∀ X0 : G, (k X0 (k (σ y) (σ (M.op x y)))) = (τ (k (σ X0) (σ (σ (M.op x y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1535 eq59
    | exact resolve eq59 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1589 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (k (σ y) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1568 X0
       have i₂ := eq52 X0 sF3
       grind)
    | exact superpose eq52 eq1568
    | exact resolve eq1568 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq1965 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1477 eq450
    | exact resolve eq450 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1971 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1965
  have eq1976 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1971
       have r₂ := eq48
       grind)
    | exact resolve eq1971 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq2416 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq468 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq468
       grind)
    | exact resolve eq12 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2417 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq468 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq468
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq468
       grind)
    | exact resolve eq11 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq2419 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq2417
  have eq2424 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq2416
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq2416 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq2426 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq2424
    | exact resolve eq2424 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2427 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq2426
  have eq2511 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1494 eq15
    | exact resolve eq15 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2512 : (M.op x y) ≠ (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  have eq2520 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2511
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2511
    | exact resolve eq2511 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq2522 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2520
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2520
    | exact resolve eq2520 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq2735 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2419 eq154
    | exact resolve eq154 eq2419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq2779 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2522 eq15
    | exact resolve eq15 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522
  have eq2794 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2779
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2779
    | exact resolve eq2779 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq2796 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2794
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2794
    | exact resolve eq2794 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2797 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2796
    | exact resolve eq2796 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796
  have eq2798 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2797 eq411
    | (have r₁ := eq411
       have r₂ := eq2797
       grind)
    | exact resolve eq411 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq2797
  have eq2814 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq2798
  have eq2820 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2814
       have r₂ := eq410
       grind)
    | exact resolve eq2814 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814
  have eq2847 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2820 eq132
    | (have j0 := eq132 (σ y) (σ x)
       grind)
    | (have r₁ := eq132 (σ y) (σ x)
       have r₂ := eq2820
       grind)
    | exact resolve eq132 eq2820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820
  have eq2853 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq2847
  have eq2854 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq2853
  have eq2860 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have j1 := eq131 (σ y) (σ x)
       grind)
    | (have r₁ := eq2854
       have r₂ := eq131 (σ y) (σ x)
       grind)
    | exact resolve eq2854 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq2864 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq32 eq2860
    | exact resolve eq2860 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq2865 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2864
  have eq2875 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2865 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2865
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2865
       grind)
    | exact resolve eq11 eq2865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2876 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2865
  have eq2877 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2875
  have eq2914 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2877 eq154
    | exact resolve eq154 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2915 : (σ (σ y)) = (k (σ (σ x)) (σ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2877 eq15
    | exact resolve eq15 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2933 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1422 eq2914
    | exact resolve eq2914 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914
  have eq2950 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq2933
  have eq2957 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq2950
       have r₂ := eq2876
       grind)
    | exact resolve eq2950 eq2876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950
  have eq2976 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2957 eq15
    | exact resolve eq15 eq2957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2978 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq26 eq2976
    | exact resolve eq2976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq2979 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq2978
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2978
    | exact resolve eq2978 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2978
  have eq2987 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2979 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2979
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2979
       grind)
    | exact resolve eq12 eq2979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979
  have eq2989 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2987
  have eq2996 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq32 eq2989
    | exact resolve eq2989 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2989
  have eq2997 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2996
  have eq3033 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2997 eq154
    | exact resolve eq154 eq2997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq3046 : ∀ X0 : G, (τ (k (σ (σ y)) (σ X0))) = (k (k (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq2915 eq54
    | exact resolve eq54 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq3064 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3046 x
       have i₂ := eq52 sF5 x
       grind)
    | exact superpose eq52 eq3046
    | exact resolve eq3046 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046
  have eq3109 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1422 eq3033
    | exact resolve eq3033 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq3033
  have eq3135 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq3109
  have eq3277 : (k (σ y) (k (σ y) (σ (M.op x y)))) = (k (k (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq3064 eq1589
    | exact resolve eq1589 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq3285 : (k (σ y) (k (σ y) (σ (M.op x y)))) = (k (k (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq3277
  have eq3301 : (k (σ y) (k (σ y) (σ (M.op x y)))) = (k (k (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq3285
       have r₂ := eq2876
       grind)
    | exact resolve eq3285 eq2876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq3403 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3135 eq15
    | exact resolve eq15 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3406 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3403
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq3403
    | exact resolve eq3403 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3407 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq3406
    | exact resolve eq3406 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3406
  have eq3415 : (σ (σ (M.op x y))) = (k (σ (σ x)) (σ (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3407 eq15
    | exact resolve eq15 eq3407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3407
  have eq4094 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1447 eq2957
    | exact resolve eq2957 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2957
  have eq4099 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1447 eq15
    | exact resolve eq15 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq4105 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) := by grind
  clear eq4094
  have eq4109 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4099
    | exact resolve eq4099 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4099
  have eq4110 : (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq4105
       have r₂ := eq2876
       grind)
    | exact resolve eq4105 eq2876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105
  have eq4112 : (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4109
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq4109
    | exact resolve eq4109 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq5689 : ∀ X0 : G, (τ (k (σ (σ (M.op x y))) (σ X0))) = (k (k (σ x) (σ (M.op x y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq3415 eq54
    | exact resolve eq54 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415
  have eq5715 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (k (σ x) (σ (M.op x y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5689 x
       have i₂ := eq52 sF3 x
       grind)
    | exact superpose eq52 eq5689
    | exact resolve eq5689 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5689
  have eq6151 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq559
  have eq7334 : (k (σ y) (σ x)) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have j0 := eq588 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq12671 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2735 eq545
    | exact resolve eq545 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq2735
  have eq12686 : (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq12671
  have eq16174 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq647 eq11
    | (have j0 := eq11 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq11 (τ (σ x)) (τ (σ y))
       have r₂ := eq647
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq647
       grind)
    | exact resolve eq11 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq16176 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16174
  have eq16403 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2877 eq6151
    | (have r₁ := eq6151
       have r₂ := eq2877
       grind)
    | exact resolve eq6151 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877 eq6151
  have eq16413 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16403
  have eq16414 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16413
  have eq16421 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16414
       have r₂ := eq48
       grind)
    | exact resolve eq16414 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16414
  have eq17711 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (k (σ y) (σ x)) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq7334 eq13
    | (have j0 := eq13 (k (σ y) (σ x)) (σ x)
       grind)
    | (have r₁ := eq13 (k (σ y) (σ x)) (σ x)
       have r₂ := eq7334
       grind)
    | (have r₁ := eq13 (σ x) (k (σ y) (σ x))
       have r₂ := eq7334
       grind)
    | exact resolve eq13 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17714 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq7334
  have eq17716 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (k (σ y) (σ x)) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq17711
  have eq17717 : (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (k (σ y) (σ x)) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq17716
  have eq17729 : (k (k (σ y) (σ x)) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq17717
       have r₂ := eq17714
       grind)
    | exact resolve eq17717 eq17714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17714 eq17717
  have eq17868 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16421 eq138
    | (have j0 := eq138 (σ y) (σ x)
       grind)
    | (have r₁ := eq138 (σ y) (σ x)
       have r₂ := eq16421
       grind)
    | exact resolve eq138 eq16421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16421
  have eq17877 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17868
  have eq17878 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17877
  have eq17909 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq17878
       have r₂ := eq79
       grind)
    | exact resolve eq17878 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17878
  have eq17915 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq17909
       have r₂ := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq17909
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq17909 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17909
  have eq18025 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4112 eq1446
    | exact resolve eq1446 eq4112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112
  have eq18026 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq4110 eq1446
    | exact resolve eq1446 eq4110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq4110
  have eq18039 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq18026
  have eq18040 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq18025
  have eq18044 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq18039
       have r₂ := eq2876
       grind)
    | exact resolve eq18039 eq2876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18039
  have eq18055 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq18044 eq15
    | exact resolve eq15 eq18044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18044
  have eq18068 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18055
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq18055
    | exact resolve eq18055 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18055
  have eq18069 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq26 eq18068
    | exact resolve eq18068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068
  have eq18077 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq18069 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18069
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18069
       grind)
    | exact resolve eq13 eq18069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18078 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq18069 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18069
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18069
       grind)
    | exact resolve eq12 eq18069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18069
  have eq18080 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq18078
  have eq18081 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq18077
  have eq18088 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq32 eq18080
    | exact resolve eq18080 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18080
  have eq18089 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq18088
  have eq18090 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq32 eq18081
    | exact resolve eq18081 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18081
  have eq18091 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq18090
  have eq18094 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq32 eq18091
    | exact resolve eq18091 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18091
  have eq18239 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq18089 eq154
    | exact resolve eq154 eq18089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18089
  have eq18390 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq18094 eq48
    | (have r₁ := eq48
       have r₂ := eq18094
       grind)
    | exact resolve eq48 eq18094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18094
  have eq18399 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq18390
       have r₂ := eq48
       grind)
    | exact resolve eq18390 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18390
  have eq18623 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq18040 eq15
    | exact resolve eq15 eq18040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18040
  have eq18636 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq18623
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq18623
    | exact resolve eq18623 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18623
  have eq18637 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq26 eq18636
    | exact resolve eq18636 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18636
  have eq18646 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq18637 eq5715
    | exact resolve eq5715 eq18637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5715 eq18637
  have eq18694 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq18646 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18646
  have eq25327 : (k (τ (σ y)) (τ (σ x))) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ x)))) ∨ (τ (σ x)) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have j0 := eq1024 (τ (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq33978 : (k (σ y) (σ (M.op x y))) = (k (σ y) (k (σ y) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq3301 eq3064
    | exact resolve eq3064 eq3301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3064 eq3301
  have eq33999 : (k (σ y) (σ (M.op x y))) = (k (σ y) (k (σ y) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq33978
  have eq34038 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1516 eq33999
    | exact resolve eq33999 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33999
  have eq34066 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq34038
  have eq34074 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq34066
       have r₂ := eq2876
       grind)
    | exact resolve eq34066 eq2876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2876 eq34066
  have eq34108 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34074 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq34074
       grind)
    | exact resolve eq11 eq34074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34074
  have eq34120 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq34108
       have r₂ := eq1516
       grind)
    | exact resolve eq34108 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516 eq34108
  have eq34130 : (σ y) ≠ (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34120 eq1300
    | (have r₁ := eq1300
       have r₂ := eq34120
       grind)
    | exact resolve eq1300 eq34120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq34120
  have eq34188 : (σ y) ≠ (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by grind
  clear eq34130
  have eq34189 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq34188
  have eq47871 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq12686 eq557
    | (have r₁ := eq557
       have r₂ := eq12686
       grind)
    | exact resolve eq557 eq12686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12686
  have eq47975 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq47871
  have eq47976 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq47975
  have eq47999 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq47976
       have r₂ := eq48
       grind)
    | exact resolve eq47976 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47976
  have eq55120 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (k (τ (σ x)) (τ (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq1359 eq15
    | exact resolve eq15 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq55385 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ (τ (σ x))) (σ (τ (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55120 X0
       have i₂ := eq15 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq15 eq55120
    | exact resolve eq55120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55120
  have eq55391 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ (τ (σ x))) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55385 X0
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq55385
    | exact resolve eq55385 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55385
  have eq55392 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55391 X0
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq55391
    | exact resolve eq55391 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55391
  have eq55393 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (k (σ X0) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55392 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq55392
    | exact resolve eq55392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55392
  have eq55394 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (k (σ X0) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq55393
    | (have j0 := eq55393 X0
       grind)
    | exact resolve eq55393 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55393
  have eq56100 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (k X0 (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55394 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq55394
    | exact resolve eq55394 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55394
  have eq56476 : (σ (M.op x y)) = (k (σ y) (k (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq56100 eq34189
    | exact resolve eq34189 eq56100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34189 eq56100
  have eq56487 : (σ (M.op x y)) = (k (σ y) (k (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq56476
  have eq56825 : (σ (τ (σ y))) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16176 eq15
    | exact resolve eq15 eq16176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16176
  have eq56866 : (σ y) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56825
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq56825
    | exact resolve eq56825 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56825
  have eq56875 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56866
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq56866
    | exact resolve eq56866 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56866
  have eq57460 : (σ y) ≠ (k (σ y) (k (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq56487
  have eq62880 : (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1976 eq443
    | exact resolve eq443 eq1976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq63074 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq62880
  have eq63233 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq63074 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq63074
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq63074
       grind)
    | exact resolve eq13 eq63074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63074
  have eq63237 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq63233
  have eq63238 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq63237
  have eq63250 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq63238
    | exact resolve eq63238 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63238
  have eq63251 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq63250
  have eq63253 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq63251
    | exact resolve eq63251 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63251
  have eq63256 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq63253 eq33
    | exact resolve eq33 eq63253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63261 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq63253 eq1468
    | exact resolve eq1468 eq63253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq63262 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq63253
  have eq63263 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq63261
  have eq63264 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq63263
       have r₂ := eq63262
       grind)
    | exact resolve eq63263 eq63262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63262 eq63263
  have eq63384 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq63264 eq557
    | (have r₁ := eq557
       have r₂ := eq63264
       grind)
    | exact resolve eq557 eq63264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq63264
  have eq63500 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq63384
  have eq63501 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq63500
  have eq63540 : (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq63501 eq443
    | exact resolve eq443 eq63501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63501
  have eq63731 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq63540
  have eq63767 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq463 eq17729
    | exact resolve eq17729 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17729
  have eq63809 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq63767
  have eq63826 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq63809
       have r₂ := eq98
       grind)
    | exact resolve eq63809 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63809
  have eq63837 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq63826
    | exact resolve eq63826 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63826
  have eq63838 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq63837
  have eq64016 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq63731 eq35
    | exact resolve eq35 eq63731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63731
  have eq64196 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq64016
    | exact resolve eq64016 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64016
  have eq64197 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq64196
  have eq64213 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64197 eq35
    | exact resolve eq35 eq64197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64197
  have eq64227 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq64213
    | exact resolve eq64213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64213
  have eq64228 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq64227
  have eq64266 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq64228 eq79
    | (have r₁ := eq79
       have r₂ := eq64228
       grind)
    | exact resolve eq79 eq64228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64267 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq64228 eq98
    | (have r₁ := eq98
       have r₂ := eq64228
       grind)
    | exact resolve eq98 eq64228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64228
  have eq64268 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq64267
  have eq64269 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq64268
  have eq64270 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq64266
  have eq64787 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq64270 eq64269
    | exact resolve eq64269 eq64270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64269 eq64270
  have eq64817 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq64787
  have eq65224 : (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq64817 eq15
    | exact resolve eq15 eq64817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65513 : (σ (σ (σ y))) = (k (σ (σ (σ y))) (σ (σ (σ x)))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq65224 eq15
    | exact resolve eq15 eq65224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65224
  have eq67708 : (σ (σ (σ (σ y)))) = (k (σ (σ (σ (σ y)))) (σ (σ (σ (σ x))))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq65513 eq15
    | exact resolve eq15 eq65513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65513
  have eq68016 : (k (σ y) (σ x)) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have j0 := eq773 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq68924 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq63838 eq450
    | exact resolve eq450 eq63838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63838
  have eq68958 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq68924
  have eq68979 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq68958
       have r₂ := eq48
       grind)
    | exact resolve eq68958 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68958
  have eq69185 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq68979 eq154
    | exact resolve eq154 eq68979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68979
  have eq69337 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq69185
       have r₂ := eq47
       grind)
    | exact resolve eq69185 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69185
  have eq69378 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69337 eq433
    | exact resolve eq433 eq69337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69454 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69337 eq15
    | exact resolve eq15 eq69337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69337
  have eq69553 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq69378
  have eq69579 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq69454
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq69454
    | exact resolve eq69454 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69454
  have eq69584 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq69579
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq69579
    | exact resolve eq69579 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69579
  have eq69622 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69584 eq412
    | (have r₁ := eq412
       have r₂ := eq69584
       grind)
    | exact resolve eq412 eq69584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69724 : (σ (σ x)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69584 eq15
    | exact resolve eq15 eq69584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69584
  have eq69854 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq69622
  have eq69855 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq69854
  have eq69902 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69855 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq69855
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq69855
       grind)
    | exact resolve eq13 eq69855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69903 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69855 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq69855
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq69855
       grind)
    | exact resolve eq12 eq69855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69904 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69855 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq69855
       grind)
    | exact resolve eq11 eq69855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69855
  have eq69905 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq69903
  have eq69906 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq69902
  have eq69921 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq69905
    | exact resolve eq69905 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69905
  have eq69922 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq69921
  have eq69923 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq69906
    | exact resolve eq69906 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69906
  have eq69924 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq69923
  have eq69927 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq69924
    | exact resolve eq69924 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69924
  have eq70029 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69922 eq154
    | exact resolve eq154 eq69922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69922
  have eq70394 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69927 eq48
    | (have r₁ := eq48
       have r₂ := eq69927
       grind)
    | exact resolve eq48 eq69927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70405 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq70394
       have r₂ := eq48
       grind)
    | exact resolve eq70394 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70394
  have eq70584 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1449 eq70029
    | exact resolve eq70029 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq70690 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq70584
  have eq71889 : ∀ X0 : G, (k X0 (k (σ y) (σ x))) = (τ (k (σ X0) (σ (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq69724 eq59
    | exact resolve eq59 eq69724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71890 : ∀ X0 : G, (k (k (σ y) (σ x)) X0) = (τ (k (σ (σ x)) (σ X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq69724 eq54
    | exact resolve eq54 eq69724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69724
  have eq72019 : ∀ X0 : G, (k (σ x) X0) = (k (k (σ y) (σ x)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq71890 x
       have i₂ := eq52 sF4 x
       grind)
    | exact superpose eq52 eq71890
    | exact resolve eq71890 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71890
  have eq72020 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq71889 X0
       have i₂ := eq52 X0 sF4
       grind)
    | exact superpose eq52 eq71889
    | exact resolve eq71889 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71889
  have eq72070 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq70690 eq1467
    | exact resolve eq1467 eq70690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq70690
  have eq72122 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq72070
  have eq72314 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72122 eq35
    | exact resolve eq35 eq72122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72122
  have eq72427 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq72314
    | exact resolve eq72314 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72314
  have eq72428 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq72427
  have eq72448 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq69927 eq72428
    | exact resolve eq72428 eq69927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69927
  have eq72452 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq72428 eq98
    | (have r₁ := eq98
       have r₂ := eq72428
       grind)
    | exact resolve eq98 eq72428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72454 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq72452
  have eq72455 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq72454
  have eq72457 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq72448
  have eq72463 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq72457
       have r₂ := eq69904
       grind)
    | exact resolve eq72457 eq69904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69904 eq72457
  have eq73518 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq72455 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq72455
       grind)
    | exact resolve eq12 eq72455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73548 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq73518
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq73518 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73518
  have eq73557 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq73548
    | exact resolve eq73548 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73548
  have eq73558 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq73557
  have eq74593 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq72463
  have eq74649 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq74593
       have r₂ := eq72428
       grind)
    | exact resolve eq74593 eq72428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72428 eq74593
  have eq74718 : (σ y) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq74649 eq57460
    | exact resolve eq57460 eq74649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57460
  have eq74723 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq74649 eq70405
    | (have r₁ := eq70405
       have r₂ := eq74649
       grind)
    | exact resolve eq70405 eq74649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70405
  have eq74731 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq74649 eq154
    | exact resolve eq154 eq74649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74649
  have eq74756 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq74723
  have eq74757 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq74756
  have eq74763 : (σ y) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq74718
  have eq74831 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq74757
       have r₂ := eq48
       grind)
    | exact resolve eq74757 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74757
  have eq74832 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq74763
       have r₂ := eq463
       grind)
    | exact resolve eq74763 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74763
  have eq75160 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq443 eq74831
    | exact resolve eq74831 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq75297 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq74831 eq154
    | exact resolve eq154 eq74831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74831
  have eq75454 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq75160
  have eq76359 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq75297 eq433
    | exact resolve eq433 eq75297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76377 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq75297 eq926
    | exact resolve eq926 eq75297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926 eq75297
  have eq76520 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq76377
  have eq76538 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq76359
  have eq76838 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq75454
  have eq77097 : (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq76838
       have r₂ := eq76538
       grind)
    | exact resolve eq76838 eq76538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76538 eq76838
  have eq77395 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq77097 eq35
    | exact resolve eq35 eq77097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77585 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq77395
    | exact resolve eq77395 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77395
  have eq77586 : (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq77585
  have eq77589 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq77586 eq47
    | (have r₁ := eq47
       have r₂ := eq77586
       grind)
    | exact resolve eq47 eq77586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77639 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq77589
  have eq77693 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq77639 eq15
    | exact resolve eq15 eq77639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77639
  have eq77722 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq77693
    | exact resolve eq77693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77693
  have eq77723 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq77722
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq77722
    | exact resolve eq77722 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77722
  have eq78634 : (k (τ (σ y)) (τ (σ x))) ≠ (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (k (k (τ (σ y)) (τ (σ x))) (τ (σ x))) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq25327 eq13
    | (have j0 := eq13 (k (τ (σ y)) (τ (σ x))) (τ (σ x))
       grind)
    | (have r₁ := eq13 (k (τ (σ y)) (τ (σ x))) (τ (σ x))
       have r₂ := eq25327
       grind)
    | (have r₁ := eq13 (τ (σ x)) (k (τ (σ y)) (τ (σ x)))
       have r₂ := eq25327
       grind)
    | exact resolve eq13 eq25327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25327
  have eq78639 : (k (τ (σ y)) (τ (σ x))) ≠ (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (k (k (τ (σ y)) (τ (σ x))) (τ (σ x))) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq78634
  have eq78640 : (τ (σ x)) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (k (k (τ (σ y)) (τ (σ x))) (τ (σ x))) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq78639
  have eq78662 : (k (k (τ (σ y)) (τ (σ x))) (τ (σ x))) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (k (τ (σ y)) (τ (σ x))) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (k (τ (σ y)) (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq78640
       have r₂ := eq47
       grind)
    | exact resolve eq78640 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78640
  have eq86295 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq74832 eq42
    | exact resolve eq42 eq74832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86676 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq74832 eq74731
    | exact resolve eq74731 eq74832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74731 eq74832
  have eq86707 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq86676
  have eq96083 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq69553 eq72019
    | exact resolve eq72019 eq69553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72019
  have eq96599 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq96083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96083
  have eq96735 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq69553 eq72020
    | exact resolve eq72020 eq69553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72020
  have eq97276 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq96735 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96735
  have eq101579 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq86295 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq86295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86295
  have eq101585 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq101579
  have eq117658 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq86707 eq101585
    | exact resolve eq101585 eq86707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86707 eq101585
  have eq117689 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq117658
  have eq117989 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq117689 eq35
    | exact resolve eq35 eq117689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117689
  have eq118216 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq26 eq117989
    | exact resolve eq117989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117989
  have eq118217 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq118216
  have eq118221 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq118217 eq47
    | (have r₁ := eq47
       have r₂ := eq118217
       grind)
    | exact resolve eq47 eq118217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118240 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq118217 eq70029
    | exact resolve eq70029 eq118217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70029 eq118217
  have eq118290 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq118240
  have eq118309 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq118221
  have eq118494 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq118309 eq15
    | exact resolve eq15 eq118309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118532 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq118494
    | exact resolve eq118494 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118494
  have eq118533 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq118532
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq118532
    | exact resolve eq118532 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118532
  have eq121609 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq118290 eq118309
    | exact resolve eq118309 eq118290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118290 eq118309
  have eq121649 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq121609
  have eq121920 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq121649 eq35
    | exact resolve eq35 eq121649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121649
  have eq122071 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq121920
    | exact resolve eq121920 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121920
  have eq122072 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq122071
  have eq122122 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123 eq122072
    | exact resolve eq122072 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq122130 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq122072 eq48
    | (have r₁ := eq48
       have r₂ := eq122072
       grind)
    | exact resolve eq48 eq122072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122131 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq122072 eq79
    | (have r₁ := eq79
       have r₂ := eq122072
       grind)
    | exact resolve eq79 eq122072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122133 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq122072
  have eq122135 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq122131
  have eq122138 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq122130
       have r₂ := eq48
       grind)
    | exact resolve eq122130 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122130
  have eq122139 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq122122
       have r₂ := eq48
       grind)
    | exact resolve eq122122 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122122
  have eq122631 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq122135 eq72455
    | exact resolve eq72455 eq122135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72455
  have eq122634 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq122135 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq122135
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq122135
       grind)
    | exact resolve eq11 eq122135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122135
  have eq122635 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq122634
  have eq122637 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq122631
  have eq122663 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq122637
       have r₂ := eq122133
       grind)
    | exact resolve eq122637 eq122133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122637
  have eq122722 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq122635 eq154
    | exact resolve eq154 eq122635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127931 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq122139 eq154
    | exact resolve eq154 eq122139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122139
  have eq147307 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq77586 eq127931
    | exact resolve eq127931 eq77586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127931
  have eq147432 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq147307
  have eq147452 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq147432
       have r₂ := eq122138
       grind)
    | exact resolve eq147432 eq122138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147432
  have eq148432 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq147452 eq15
    | exact resolve eq15 eq147452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147452
  have eq148516 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq148432
    | exact resolve eq148432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148432
  have eq148540 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq148516
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq148516
    | exact resolve eq148516 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148516
  have eq148607 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq148540 eq77723
    | exact resolve eq77723 eq148540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77723 eq148540
  have eq148686 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq148607
  have eq148733 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq148686
       have r₂ := eq122138
       grind)
    | exact resolve eq148686 eq122138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122138 eq148686
  have eq148947 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq148733 eq154
    | exact resolve eq154 eq148733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148733
  have eq149526 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq148947 eq1494
    | exact resolve eq1494 eq148947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148947
  have eq149677 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq149526
  have eq174951 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq97276 eq133
    | (have j0 := eq133 (σ y)
       grind)
    | exact resolve eq133 eq97276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97276
  have eq175943 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq174951
       have r₂ := eq69553
       grind)
    | exact resolve eq174951 eq69553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69553 eq174951
  have eq175970 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq175943 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | (have r₁ := eq11 (σ y) (σ y)
       have r₂ := eq175943
       grind)
    | exact resolve eq11 eq175943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175943
  have eq175971 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq175970
  have eq175991 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq175971 eq96599
    | exact resolve eq96599 eq175971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96599 eq175971
  have eq176050 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq175991
  have eq176161 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq176050 eq132
    | (have j0 := eq132 (σ y) (σ x)
       grind)
    | (have r₁ := eq132 (σ y) (σ x)
       have r₂ := eq176050
       grind)
    | exact resolve eq132 eq176050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176050
  have eq176186 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq176161
  have eq176187 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq176186
  have eq176262 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq32 eq176187
    | exact resolve eq176187 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176187
  have eq176263 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq176262
  have eq176293 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq176263
  have eq176313 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq176293
       have r₂ := eq77097
       grind)
    | exact resolve eq176293 eq77097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176293
  have eq176350 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq176313 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq176313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176313
  have eq176378 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq176350
       have r₂ := eq77097
       grind)
    | exact resolve eq176350 eq77097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77097 eq176350
  have eq176445 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq176378 eq154
    | exact resolve eq154 eq176378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176378
  have eq176700 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq176445 eq132
    | (have j0 := eq132 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq132 (τ (σ y)) (τ (σ x))
       have r₂ := eq176445
       grind)
    | exact resolve eq132 eq176445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176445
  have eq176723 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq176700
  have eq176764 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq42 eq176723
    | exact resolve eq176723 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176723
  have eq176765 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq176764
  have eq211775 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1343 eq56875
    | exact resolve eq56875 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343 eq56875
  have eq211999 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq211775
  have eq212007 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq211999
       have r₂ := eq459
       grind)
    | exact resolve eq211999 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211999
  have eq212011 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have j1 := eq133 (τ (σ x))
       grind)
    | (have r₁ := eq212007
       have r₂ := eq133 (τ (σ x))
       grind)
    | exact resolve eq212007 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212007
  have eq229333 : (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1362 eq212011
    | exact resolve eq212011 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362 eq212011
  have eq229342 : (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq229333
  have eq229344 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq229342
       have r₂ := eq459
       grind)
    | exact resolve eq229342 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq229342
  have eq229409 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq229344 eq154
    | exact resolve eq154 eq229344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229344
  have eq229726 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq229409 eq659
    | exact resolve eq659 eq229409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq229806 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq229726
  have eq229897 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq229806 eq42
    | exact resolve eq42 eq229806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230615 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq229806 eq229409
    | exact resolve eq229409 eq229806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229806
  have eq230618 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq230615
  have eq231544 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq229897 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq229897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229897
  have eq231550 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq231544
  have eq231637 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq231550 eq15
    | exact resolve eq15 eq231550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231679 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq231637
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq231637
    | exact resolve eq231637 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231637
  have eq231680 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq26 eq231679
    | exact resolve eq231679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231679
  have eq232044 : (k (σ x) (σ x)) = (k (σ y) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq231680 eq118533
    | exact resolve eq118533 eq231680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118533 eq231680
  have eq232151 : (k (σ x) (σ x)) = (k (σ y) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq232044
  have eq232592 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq230618 eq231550
    | exact resolve eq231550 eq230618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230618 eq231550
  have eq232633 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq232592
  have eq232644 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq232633 eq78
    | (have r₁ := eq78
       have r₂ := eq232633
       grind)
    | exact resolve eq78 eq232633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232807 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq232633 eq18239
    | exact resolve eq18239 eq232633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18239
  have eq233201 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq232807
  have eq233369 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq232644
  have eq233493 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq233201 eq15
    | exact resolve eq15 eq233201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233201
  have eq233533 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq233493
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq233493
    | exact resolve eq233493 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233493
  have eq233534 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq26 eq233533
    | exact resolve eq233533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233533
  have eq233535 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq233534
  have eq234274 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq233535 eq131
    | (have j0 := eq131 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq131 (σ x) (σ (M.op x y))
       have r₂ := eq233535
       grind)
    | exact resolve eq131 eq233535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234307 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq234274
  have eq240647 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq47999 eq154
    | exact resolve eq154 eq47999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47999
  have eq240889 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq240647
       have r₂ := eq47
       grind)
    | exact resolve eq240647 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240647
  have eq245834 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq233369 eq15
    | exact resolve eq15 eq233369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233369
  have eq245901 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq26 eq245834
    | exact resolve eq245834 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245834
  have eq245902 : (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq245901
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq245901
    | exact resolve eq245901 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245901
  have eq245921 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq245902 eq11
    | (have j0 := eq11 (τ (σ x)) (M.op x y)
       grind)
    | (have r₁ := eq11 (τ (σ x)) (M.op x y)
       have r₂ := eq245902
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq245902
       grind)
    | exact resolve eq11 eq245902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245902
  have eq245922 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq245921
  have eq245958 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq245922 eq15
    | exact resolve eq15 eq245922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245922
  have eq246025 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq26 eq245958
    | exact resolve eq245958 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245958
  have eq246026 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq246025
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq246025
    | exact resolve eq246025 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246025
  have eq263232 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq234307 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq11 (σ (M.op x y)) (σ x)
       have r₂ := eq234307
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq234307
       grind)
    | exact resolve eq11 eq234307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263233 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq234307
  have eq263234 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq263232
  have eq263446 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq263234 eq233535
    | exact resolve eq233535 eq263234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233535 eq263234
  have eq263515 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq263446
  have eq263582 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq263515
       have r₂ := eq263233
       grind)
    | exact resolve eq263515 eq263233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263233 eq263515
  have eq263594 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq263582 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq263582
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq263582
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ x)
       have r₂ := eq263582
       grind)
    | exact resolve eq13 eq263582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263582
  have eq263598 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq263594
  have eq263599 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq263598
  have eq266292 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq263599 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq263599
       grind)
    | exact resolve eq11 eq263599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266293 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq263599
  have eq274213 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (k (σ y) (σ x)) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq68016 eq13
    | (have j0 := eq13 (k (σ y) (σ x)) (σ x)
       grind)
    | (have r₁ := eq13 (k (σ y) (σ x)) (σ x)
       have r₂ := eq68016
       grind)
    | (have r₁ := eq13 (σ x) (k (σ y) (σ x))
       have r₂ := eq68016
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq68016
       grind)
    | exact resolve eq13 eq68016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68016
  have eq274218 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (k (σ y) (σ x)) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq274213
  have eq274219 : (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (k (k (σ y) (σ x)) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq274218
  have eq274264 : (k (k (σ y) (σ x)) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq274219
       have r₂ := eq48
       grind)
    | exact resolve eq274219 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274219
  have eq312881 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq904 eq76520
    | exact resolve eq76520 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313797 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq312881
  have eq313879 : (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq313797
       have r₂ := eq915
       grind)
    | exact resolve eq313797 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq313797
  have eq391690 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq246026 eq266292
    | (have r₁ := eq266292
       have r₂ := eq246026
       grind)
    | exact resolve eq266292 eq246026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246026 eq266292
  have eq391708 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq391690
  have eq391709 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq391708
  have eq391728 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq391709
       have r₂ := eq266293
       grind)
    | exact resolve eq391709 eq266293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266293 eq391709
  have eq391814 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq391728 eq18694
    | exact resolve eq18694 eq391728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18694 eq391728
  have eq391879 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq391814
  have eq459918 : (σ (σ (σ (σ (σ y))))) = (k (σ (σ (σ (σ (σ y))))) (σ (σ (σ (σ (σ x)))))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq67708 eq15
    | exact resolve eq15 eq67708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67708
  have eq474163 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq391879 eq232151
    | exact resolve eq232151 eq391879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232151 eq391879
  have eq474258 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq474163
  have eq474264 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq474258
       have r₂ := eq48
       grind)
    | exact resolve eq474258 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474258
  have eq474615 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq474264 eq154
    | exact resolve eq154 eq474264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474264
  have eq474935 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq474615
       have r₂ := eq47
       grind)
    | exact resolve eq474615 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474615
  have eq475440 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq474935 eq15
    | exact resolve eq15 eq474935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474935
  have eq475716 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq475440
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq475440
    | exact resolve eq475440 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475440
  have eq475754 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq475716
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq475716
    | exact resolve eq475716 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475716
  have eq475794 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq475754 eq412
    | (have r₁ := eq412
       have r₂ := eq475754
       grind)
    | exact resolve eq412 eq475754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476302 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq475794
  have eq476303 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq476302
  have eq477163 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq476303 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq476303
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq476303
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq476303
       grind)
    | exact resolve eq12 eq476303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476303
  have eq477165 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq477163
  have eq477198 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq32 eq477165
    | exact resolve eq477165 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477165
  have eq477199 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq477198
  have eq477460 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq477199 eq475754
    | exact resolve eq475754 eq477199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475754 eq477199
  have eq477544 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq477460
  have eq507569 : (k (τ (σ y)) (τ (σ x))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq445 eq78662
    | exact resolve eq78662 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78662
  have eq507640 : (k (τ (σ y)) (τ (σ x))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq507569
  have eq507675 : (k (τ (σ y)) (τ (σ x))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq507640
       have r₂ := eq97
       grind)
    | exact resolve eq507640 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507640
  have eq507700 : (M.op x y) = (τ (σ x)) ∨ (k (τ (σ y)) (τ (σ x))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq42 eq507675
    | exact resolve eq507675 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507675
  have eq507701 : (k (τ (σ y)) (τ (σ x))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq507700
  have eq927662 : (τ (σ x)) ≠ (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq176765 eq12
    | (have j0 := eq12 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq12 (τ (σ y)) (τ (σ x))
       have r₂ := eq176765
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq176765
       grind)
    | exact resolve eq12 eq176765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176765
  have eq927682 : (τ (σ x)) ≠ (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have j1 := eq12 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq927662
       have r₂ := eq12 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq927662
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq927662 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927662
  have eq927684 : (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq42 eq927682
    | exact resolve eq927682 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927682
  have eq927685 : (τ (σ x)) ≠ (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq927684
  have eq1161430 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq149677 eq132
    | (have j0 := eq132 (σ y) (σ x)
       grind)
    | (have r₁ := eq132 (σ y) (σ x)
       have r₂ := eq149677
       grind)
    | exact resolve eq132 eq149677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149677
  have eq1161516 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1161430
  have eq1161517 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1161516
  have eq1161702 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq131 (σ y) (σ x)
       grind)
    | (have r₁ := eq1161517
       have r₂ := eq131 (σ y) (σ x)
       grind)
    | exact resolve eq1161517 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161517
  have eq1161716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32 eq1161702
    | exact resolve eq1161702 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161702
  have eq1161717 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1161716
  have eq1162319 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1161717
  have eq1162358 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1162319
       have r₂ := eq77586
       grind)
    | exact resolve eq1162319 eq77586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162319
  have eq1162546 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1162358 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1162358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162358
  have eq1162585 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1162546
       have r₂ := eq77586
       grind)
    | exact resolve eq1162546 eq77586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77586 eq1162546
  have eq1162752 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1162585 eq154
    | exact resolve eq154 eq1162585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162585
  have eq1390649 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq240889 eq445
    | exact resolve eq445 eq240889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1390959 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq240889 eq15
    | exact resolve eq15 eq240889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240889
  have eq1391342 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1390649
  have eq1391403 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1390959
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1390959
    | exact resolve eq1390959 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390959
  have eq1391451 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1391403
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1391403
    | exact resolve eq1391403 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391403
  have eq1391496 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1391342 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1391342
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1391342
       grind)
    | exact resolve eq13 eq1391342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391342
  have eq1391500 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1391496
  have eq1391501 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1391500
  have eq1391545 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq1391501
    | exact resolve eq1391501 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391501
  have eq1391546 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1391545
  have eq1391548 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq1391546
    | exact resolve eq1391546 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391546
  have eq1391551 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1391548 eq33
    | exact resolve eq33 eq1391548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391548
  have eq1391566 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq1391551
       have r₂ := eq904
       grind)
    | exact resolve eq1391551 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq1391551
  have eq1392821 : (k (σ y) (σ x)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1391566 eq63256
    | exact resolve eq63256 eq1391566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63256
  have eq1392840 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1391566 eq76520
    | exact resolve eq76520 eq1391566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76520 eq1391566
  have eq1394347 : (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq1392840
  have eq1394366 : (k (σ y) (σ x)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1392821
  have eq1394929 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq1394366
       have r₂ := eq1394347
       grind)
    | exact resolve eq1394366 eq1394347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394347 eq1394366
  have eq1396153 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq507701 eq501
    | exact resolve eq501 eq507701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq507701
  have eq1396192 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) := by grind
  clear eq1396153
  have eq1396227 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have r₁ := eq1396192
       have r₂ := eq47
       grind)
    | exact resolve eq1396192 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396192
  have eq1398027 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1391451 eq412
    | (have r₁ := eq412
       have r₂ := eq1391451
       grind)
    | exact resolve eq412 eq1391451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391451
  have eq1398738 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq1398027
  have eq1398739 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq1398738
  have eq1398851 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq1398739
       have r₂ := eq410
       grind)
    | exact resolve eq1398739 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398739
  have eq1407870 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1398851 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1398851
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1398851
       grind)
    | exact resolve eq13 eq1398851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1407871 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1398851 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1398851
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1398851
       grind)
    | exact resolve eq12 eq1398851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398851
  have eq1407873 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1407871
  have eq1407874 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1407870
  have eq1407875 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1407874
  have eq1407919 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq1407873
    | exact resolve eq1407873 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407873
  have eq1407920 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1407919
  have eq1407921 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq1407875
    | exact resolve eq1407875 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407875
  have eq1407922 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1407921
  have eq1407930 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq1407922
    | exact resolve eq1407922 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407922
  have eq1409001 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1407930 eq33
    | exact resolve eq33 eq1407930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407930
  have eq1419879 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq1396227 eq15
    | exact resolve eq15 eq1396227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396227
  have eq1420231 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq1419879
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1419879
    | exact resolve eq1419879 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419879
  have eq1420261 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1420231
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1420231
    | exact resolve eq1420231 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420231
  have eq1420277 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1420261 eq13
    | (have j0 := eq13 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq13 (τ (σ x)) (τ (σ y))
       have r₂ := eq1420261
       grind)
    | exact resolve eq13 eq1420261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420261
  have eq1420281 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1420277
  have eq1420282 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1420281
  have eq1420297 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq1420282
    | exact resolve eq1420282 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420282
  have eq1420298 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq1420297
  have eq1420305 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq1420298
    | exact resolve eq1420298 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420298
  have eq1420479 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq122722 eq1420305
    | exact resolve eq1420305 eq122722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122722
  have eq1420486 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq229409 eq1420305
    | exact resolve eq1420305 eq229409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229409
  have eq1420725 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1420305 eq15
    | exact resolve eq15 eq1420305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1420729 : (τ (M.op x y)) = (k (τ (τ (σ x))) (τ (τ (σ y)))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1420305 eq154
    | exact resolve eq154 eq1420305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420305
  have eq1420944 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1420486
  have eq1420951 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1420479
  have eq1420985 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1420725
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1420725
    | exact resolve eq1420725 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420725
  have eq1420998 : (σ x) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1420944
       have r₂ := eq48
       grind)
    | exact resolve eq1420944 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420944
  have eq1420999 : (σ x) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1420951
       have r₂ := eq48
       grind)
    | exact resolve eq1420951 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420951
  have eq1421019 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1420985
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1420985
    | exact resolve eq1420985 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420985
  have eq1421020 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1421019
    | exact resolve eq1421019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421019
  have eq1421059 : (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq122663 eq1421020
    | exact resolve eq1421020 eq122663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122663
  have eq1421370 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq1421020 eq1407920
    | exact resolve eq1407920 eq1421020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407920 eq1421020
  have eq1421508 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq1421370
  have eq1421722 : (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1421059
  have eq1421769 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1421508
       have r₂ := eq1409001
       grind)
    | exact resolve eq1421508 eq1409001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409001 eq1421508
  have eq1421816 : (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq1421722
       have r₂ := eq122133
       grind)
    | exact resolve eq1421722 eq122133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421722
  have eq1422987 : (k (σ y) (σ x)) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1421769 eq477544
    | exact resolve eq477544 eq1421769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477544 eq1421769
  have eq1423480 : (k (σ y) (σ x)) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq1422987
  have eq1424405 : (k (σ y) (σ x)) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq1423480
       have r₂ := eq48
       grind)
    | exact resolve eq1423480 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423480
  have eq1460305 : (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq122635 eq1421816
    | exact resolve eq1421816 eq122635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122635 eq1421816
  have eq1460840 : (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq1460305
  have eq1460890 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have r₁ := eq1460840
       have r₂ := eq122133
       grind)
    | exact resolve eq1460840 eq122133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460840
  have eq1461149 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1460890 eq154
    | exact resolve eq154 eq1460890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460890
  have eq1462678 : (τ (τ (σ x))) = (k (τ (τ (σ x))) (τ (τ (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1461149 eq154
    | exact resolve eq154 eq1461149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461149
  have eq1470428 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1420998 eq154
    | exact resolve eq154 eq1420998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420998
  have eq1470871 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1470428
       have r₂ := eq47
       grind)
    | exact resolve eq1470428 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470428
  have eq1470968 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1470871 eq445
    | exact resolve eq445 eq1470871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471283 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1470871 eq15
    | exact resolve eq15 eq1470871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471642 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1470968
  have eq1471703 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1471283
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1471283
    | exact resolve eq1471283 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471283
  have eq1471721 : (σ x) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1471703
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1471703
    | exact resolve eq1471703 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471703
  have eq1472137 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1471642 eq36
    | exact resolve eq36 eq1471642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471642
  have eq1474530 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1472137
       have i₂ := eq154 sF4 sF5
       grind)
    | exact superpose eq154 eq1472137
    | exact resolve eq1472137 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472137
  have eq1474688 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1471721 eq412
    | (have r₁ := eq412
       have r₂ := eq1471721
       grind)
    | exact resolve eq412 eq1471721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471721
  have eq1475380 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1474688
  have eq1475381 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1475380
  have eq1475475 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq1475381
       have r₂ := eq410
       grind)
    | exact resolve eq1475381 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq1475381
  have eq1475928 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1475475 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1475475
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1475475
       grind)
    | exact resolve eq12 eq1475475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475475
  have eq1475930 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1475928
  have eq1475975 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq1475930
    | exact resolve eq1475930 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475930
  have eq1475976 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1475975
  have eq1477245 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1475976 eq154
    | exact resolve eq154 eq1475976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475976
  have eq1480969 : (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1477245 eq1470871
    | exact resolve eq1470871 eq1477245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470871
  have eq1481094 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1480969
  have eq1483229 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1481094 eq36
    | exact resolve eq36 eq1481094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481094
  have eq1485564 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1483229
       have i₂ := eq154 sF4 sF5
       grind)
    | exact superpose eq154 eq1483229
    | exact resolve eq1483229 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483229
  have eq1485966 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1485564 eq1477245
    | exact resolve eq1477245 eq1485564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477245 eq1485564
  have eq1486103 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1485966
  have eq1490052 : (M.op x y) ≠ (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1486103
  have eq1491706 : (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1490052
       have r₂ := eq232633
       grind)
    | exact resolve eq1490052 eq232633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232633 eq1490052
  have eq1491953 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1491706 eq78
    | (have r₁ := eq78
       have r₂ := eq1491706
       grind)
    | exact resolve eq78 eq1491706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491706
  have eq1493251 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1491953
  have eq1502774 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1493251 eq15
    | exact resolve eq15 eq1493251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493251
  have eq1503000 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1502774
    | exact resolve eq1502774 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502774
  have eq1503006 : (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1503000
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1503000
    | exact resolve eq1503000 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503000
  have eq1503291 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1503006 eq11
    | (have j0 := eq11 (τ (σ x)) (M.op x y)
       grind)
    | (have r₁ := eq11 (τ (σ x)) (M.op x y)
       have r₂ := eq1503006
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1503006
       grind)
    | exact resolve eq11 eq1503006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503006
  have eq1503292 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1503291
  have eq1503464 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1503292 eq15
    | exact resolve eq15 eq1503292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503292
  have eq1503701 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1503464
    | exact resolve eq1503464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503464
  have eq1503702 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1503701
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1503701
    | exact resolve eq1503701 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503701
  have eq1504033 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1503702 eq138
    | (have j0 := eq138 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq138 (σ x) (σ (M.op x y))
       have r₂ := eq1503702
       grind)
    | exact resolve eq138 eq1503702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504085 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq1504124 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1504033
  have eq1504284 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq11 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq1504124
       have r₂ := eq11 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq1504124
       have r₂ := eq11 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq1504124
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq1504124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504124
  have eq1658820 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1504284 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq11 (σ (M.op x y)) (σ x)
       have r₂ := eq1504284
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1504284
       grind)
    | exact resolve eq11 eq1504284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504284
  have eq1658822 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1658820
  have eq1662515 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1658822 eq132
    | (have j0 := eq132 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq132 (σ x) (σ (M.op x y))
       have r₂ := eq1658822
       grind)
    | (have r₁ := eq132 (σ (M.op x y)) (σ x)
       have r₂ := eq1658822
       grind)
    | exact resolve eq132 eq1658822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658822
  have eq1662608 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1662515
  have eq1662609 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1662608
  have eq1662842 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq131 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq1662609
       have r₂ := eq131 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq1662609 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662609
  have eq1690497 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1662842 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq11 (σ (M.op x y)) (σ x)
       have r₂ := eq1662842
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1662842
       grind)
    | exact resolve eq11 eq1662842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662842
  have eq1690499 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1690497
  have eq1725693 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq463 eq274264
    | exact resolve eq274264 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq274264
  have eq1725835 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1725693
  have eq1725859 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1725835
       have r₂ := eq98
       grind)
    | exact resolve eq1725835 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1725835
  have eq1725883 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq1725859
    | exact resolve eq1725859 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725859
  have eq1725884 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1725883
  have eq1725917 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1725884 eq450
    | exact resolve eq450 eq1725884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq1725925 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1725884 eq17915
    | exact resolve eq17915 eq1725884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17915 eq1725884
  have eq1726055 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1725925
  have eq1726063 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1725917
  have eq1726111 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1726055
       have r₂ := eq2427
       grind)
    | exact resolve eq1726055 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427 eq1726055
  have eq1726116 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1726063
       have r₂ := eq48
       grind)
    | exact resolve eq1726063 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726063
  have eq1726149 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1726111
       have r₂ := eq48
       grind)
    | exact resolve eq1726111 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726111
  have eq1727135 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1726116 eq154
    | exact resolve eq154 eq1726116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726116
  have eq1727662 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1727135
       have r₂ := eq47
       grind)
    | exact resolve eq1727135 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727135
  have eq1728725 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1727662 eq433
    | exact resolve eq433 eq1727662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq1729048 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1727662 eq15
    | exact resolve eq15 eq1727662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727662
  have eq1729451 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1728725
  have eq1729523 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1729048
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1729048
    | exact resolve eq1729048 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729048
  have eq1729579 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1729523
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1729523
    | exact resolve eq1729523 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729523
  have eq1736593 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1729451 eq1729579
    | exact resolve eq1729579 eq1729451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729451 eq1729579
  have eq1736764 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq1736593
  have eq1737182 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq1736764 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1736764
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1736764
       grind)
    | exact resolve eq13 eq1736764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1737186 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq1737182
  have eq1737187 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq1737186
  have eq1737234 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq32 eq1737187
    | exact resolve eq1737187 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737187
  have eq1737235 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq1737234
  have eq1737237 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq32 eq1737235
    | exact resolve eq1737235 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737235
  have eq1737461 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq1737237 eq33
    | exact resolve eq33 eq1737237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737237
  have eq1826568 : (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq64817 eq1420999
    | exact resolve eq1420999 eq64817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64817 eq1420999
  have eq1827469 : (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1826568
  have eq1827796 : (σ (σ x)) = (k (σ (σ x)) (σ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1827469 eq15
    | exact resolve eq15 eq1827469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827469
  have eq1828826 : ∀ X0 : G, (k (k (σ x) (σ y)) X0) = (τ (k (σ (σ x)) (σ X0))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1827796 eq54
    | exact resolve eq54 eq1827796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828827 : ∀ X0 : G, (k X0 (k (σ x) (σ y))) = (τ (k (σ X0) (σ (σ x)))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1827796 eq59
    | exact resolve eq59 eq1827796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827796
  have eq1829190 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (k (σ x) (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1828827 X0
       have i₂ := eq52 X0 sF4
       grind)
    | exact superpose eq52 eq1828827
    | exact resolve eq1828827 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828827
  have eq1829191 : ∀ X0 : G, (k (σ x) X0) = (k (k (σ x) (σ y)) X0) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1828826 x
       have i₂ := eq52 sF4 x
       grind)
    | exact superpose eq52 eq1828826
    | exact resolve eq1828826 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828826
  have eq1874724 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1726149 eq138
    | (have j0 := eq138 (σ y) (σ x)
       grind)
    | (have r₁ := eq138 (σ y) (σ x)
       have r₂ := eq1726149
       grind)
    | (have r₁ := eq138 (σ x) (σ y)
       have r₂ := eq1726149
       grind)
    | exact resolve eq138 eq1726149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq1726149
  have eq1874829 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1874724
  have eq1874830 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1874829
  have eq1875183 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq1874830
       have r₂ := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq1874830
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq1874830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874830
  have eq1879930 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1875183 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1875183
       grind)
    | exact resolve eq11 eq1875183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875183
  have eq1879932 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1879930
  have eq1880252 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1879932 eq132
    | (have j0 := eq132 (σ y) (σ x)
       grind)
    | (have r₁ := eq132 (σ y) (σ x)
       have r₂ := eq1879932
       grind)
    | (have r₁ := eq132 (σ x) (σ y)
       have r₂ := eq1879932
       grind)
    | exact resolve eq132 eq1879932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879932
  have eq1880352 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1880252
  have eq1880353 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1880352
  have eq1880596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have j1 := eq131 (σ y) (σ x)
       grind)
    | (have r₁ := eq1880353
       have r₂ := eq131 (σ y) (σ x)
       grind)
    | exact resolve eq1880353 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880353
  have eq1880632 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq32 eq1880596
    | exact resolve eq1880596 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880596
  have eq1880718 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq1880632
  have eq1880784 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq1880718
       have r₂ := eq1736764
       grind)
    | exact resolve eq1880718 eq1736764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736764 eq1880718
  have eq1881631 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1880784 eq154
    | exact resolve eq154 eq1880784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880784
  have eq1882151 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq1881631
       have r₂ := eq47
       grind)
    | exact resolve eq1881631 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881631
  have eq1882577 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1882151 eq1474530
    | exact resolve eq1474530 eq1882151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474530 eq1882151
  have eq1882738 : (σ x) = (M.op (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq1882577
  have eq1885706 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq1882738 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1882738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882738
  have eq2160680 : (τ (τ (σ x))) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1420729 eq1462678
    | exact resolve eq1462678 eq1420729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420729 eq1462678
  have eq2160779 : (τ (τ (σ x))) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2160680
  have eq2160871 : (τ (τ (σ x))) = (τ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2160779
       have r₂ := eq48
       grind)
    | exact resolve eq2160779 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq2160779
  have eq2161844 : (τ (σ x)) = (σ (τ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2160871 eq35
    | exact resolve eq35 eq2160871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160871
  have eq2162515 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq2161844
       have i₂ := eq35 sF2
       grind)
    | exact superpose eq35 eq2161844
    | exact resolve eq2161844 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161844
  have eq2163351 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2162515 eq154
    | exact resolve eq154 eq2162515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162515
  have eq2163964 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2163351
       have r₂ := eq47
       grind)
    | exact resolve eq2163351 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163351
  have eq2167277 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2163964 eq445
    | exact resolve eq445 eq2163964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq2167625 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2163964 eq15
    | exact resolve eq15 eq2163964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163964
  have eq2168049 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2167277
  have eq2168122 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2167625
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2167625
    | exact resolve eq2167625 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167625
  have eq2168133 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2168122
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2168122
    | exact resolve eq2168122 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168122
  have eq2172069 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2168049 eq36
    | exact resolve eq36 eq2168049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168049
  have eq2174427 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2172069
       have i₂ := eq154 sF4 sF5
       grind)
    | exact superpose eq154 eq2172069
    | exact resolve eq2172069 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172069
  have eq2411914 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq313879 eq1424405
    | exact resolve eq1424405 eq313879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313879
  have eq2411924 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq1394929 eq1424405
    | exact resolve eq1424405 eq1394929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394929 eq1424405
  have eq2411998 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2411924
  have eq2412008 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq2411914
  have eq2412061 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq2411998
    | exact resolve eq2411998 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411998
  have eq2412062 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2412061
  have eq2412064 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq2412008
       have r₂ := eq1737461
       grind)
    | exact resolve eq2412008 eq1737461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737461 eq2412008
  have eq2412073 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq32 eq2412064
    | exact resolve eq2412064 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412064
  have eq2412074 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2412073
  have eq2414015 : (σ y) = (σ (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2412074 eq35
    | exact resolve eq35 eq2412074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2415938 : (σ x) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq2414015
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2414015
    | exact resolve eq2414015 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414015
  have eq2415939 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2415938
  have eq2416449 : (M.op x y) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2415939 eq42
    | exact resolve eq42 eq2415939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2416450 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2415939 eq78
    | (have r₁ := eq78
       have r₂ := eq2415939
       grind)
    | exact resolve eq78 eq2415939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2416451 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2415939 eq97
    | (have r₁ := eq97
       have r₂ := eq2415939
       grind)
    | exact resolve eq97 eq2415939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2416506 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2415939 eq2512
    | (have r₁ := eq2512
       have r₂ := eq2415939
       grind)
    | exact resolve eq2512 eq2415939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2417875 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2416506
  have eq2417876 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2417875
  have eq2417932 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2416451
  have eq2417933 : (k (M.op x y) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2417932
  have eq2417934 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2416450
  have eq2418904 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2417934 eq15
    | exact resolve eq15 eq2417934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417934
  have eq2419168 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq26 eq2418904
    | exact resolve eq2418904 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418904
  have eq2419170 : (M.op x y) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq2419168
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2419168
    | exact resolve eq2419168 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419168
  have eq2419195 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2419170 eq11
    | (have j0 := eq11 (τ (σ x)) (M.op x y)
       grind)
    | (have r₁ := eq11 (τ (σ x)) (M.op x y)
       have r₂ := eq2419170
       grind)
    | exact resolve eq11 eq2419170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2419196 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2419195
  have eq2419411 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2419196 eq15
    | exact resolve eq15 eq2419196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419196
  have eq2419725 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (M.op x y))) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq26 eq2419411
    | exact resolve eq2419411 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419411
  have eq2419733 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq2419725
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2419725
    | exact resolve eq2419725 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419725
  have eq2422199 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2412062 eq154
    | exact resolve eq154 eq2412062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412062
  have eq2422840 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2422199
       have r₂ := eq47
       grind)
    | exact resolve eq2422199 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422199
  have eq2423176 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2422840 eq1494
    | exact resolve eq1494 eq2422840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494 eq2422840
  have eq2423940 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2423176
  have eq2424121 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2423940
       have r₂ := eq1885706
       grind)
    | exact resolve eq2423940 eq1885706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885706 eq2423940
  have eq2451617 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2417876 eq15
    | exact resolve eq15 eq2417876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417876
  have eq2451841 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2451617
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2451617
    | exact resolve eq2451617 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451617
  have eq2451854 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2451841
    | exact resolve eq2451841 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451841
  have eq2452088 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2451854 eq154
    | exact resolve eq154 eq2451854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451854
  have eq2453931 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2419170 eq2417933
    | exact resolve eq2417933 eq2419170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419170
  have eq2453952 : (τ (σ x)) ≠ (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2417933
  have eq2453968 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq2453931
  have eq2454069 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2453968 eq15
    | exact resolve eq15 eq2453968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453968
  have eq2454288 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2454069
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2454069
    | exact resolve eq2454069 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454069
  have eq2454295 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq26 eq2454288
    | exact resolve eq2454288 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454288
  have eq2454908 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2454295 eq87
    | exact resolve eq87 eq2454295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq2454295
  have eq2464322 : (σ x) ≠ (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2424121
  have eq2464642 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2464322
       have r₂ := eq2412074
       grind)
    | exact resolve eq2464322 eq2412074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412074 eq2464322
  have eq2465339 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2464642 eq154
    | exact resolve eq154 eq2464642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464642
  have eq2467207 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2465339 eq1162752
    | exact resolve eq1162752 eq2465339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162752 eq2465339
  have eq2467410 : (τ (σ x)) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq2467207
  have eq2467649 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2467410 eq42
    | exact resolve eq42 eq2467410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2469454 : (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2467410 eq927685
    | (have r₁ := eq927685
       have r₂ := eq2467410
       grind)
    | exact resolve eq927685 eq2467410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927685 eq2467410
  have eq2469617 : (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq2469454
  have eq2469618 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq2469617
  have eq2472159 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2467649 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq2467649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467649
  have eq2472165 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq2472159
  have eq2476391 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2469618 eq2472165
    | exact resolve eq2472165 eq2469618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469618 eq2472165
  have eq2476542 : (M.op x y) = (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2476391
  have eq2477360 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2476542 eq35
    | exact resolve eq35 eq2476542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476542
  have eq2478182 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq26 eq2477360
    | exact resolve eq2477360 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477360
  have eq2478183 : (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2478182
  have eq2479266 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2478183 eq35
    | exact resolve eq35 eq2478183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478183
  have eq2479980 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq2479266
    | exact resolve eq2479266 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479266
  have eq2480046 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2479980 eq79
    | (have r₁ := eq79
       have r₂ := eq2479980
       grind)
    | exact resolve eq79 eq2479980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq2479980
  have eq2480049 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2480046
  have eq2489086 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2480049 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2480049
       grind)
    | exact resolve eq11 eq2480049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480049
  have eq2489087 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2489086
  have eq2489476 : (σ (σ y)) = (k (σ (σ x)) (σ (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2489087 eq15
    | exact resolve eq15 eq2489087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2489544 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  have eq2506004 : ∀ X0 : G, (τ (k (σ (σ y)) (σ X0))) = (k (k (σ x) (σ y)) X0) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2489476 eq54
    | exact resolve eq54 eq2489476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq2506005 : ∀ X0 : G, (τ (k (σ X0) (σ (σ y)))) = (k X0 (k (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2489476 eq59
    | exact resolve eq59 eq2489476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq2489476
  have eq2506236 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2506005 X0
       have i₂ := eq52 X0 sF5
       grind)
    | exact superpose eq52 eq2506005
    | exact resolve eq2506005 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506005
  have eq2506237 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ x) (σ y)) X0) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2506004 x
       have i₂ := eq52 sF5 x
       grind)
    | exact superpose eq52 eq2506004
    | exact resolve eq2506004 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2506004
  have eq2530377 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1829190 eq2506236
    | exact resolve eq2506236 eq1829190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829190 eq2506236
  have eq2531996 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2530377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530377
  have eq2532165 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have j0 := eq2531996 X0
       grind)
    | (have r₁ := eq2531996 X0
       have r₂ := eq2489544
       grind)
    | exact resolve eq2531996 eq2489544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531996
  have eq2532372 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1829191 eq2506237
    | exact resolve eq2506237 eq1829191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829191 eq2506237
  have eq2533925 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2532372 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532372
  have eq2534080 : ∀ X0 : G, (k (σ x) X0) = (k (σ y) X0) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have j0 := eq2533925 X0
       grind)
    | (have r₁ := eq2533925 X0
       have r₂ := eq2489544
       grind)
    | exact resolve eq2533925 eq2489544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2533925
  have eq2811166 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2534080 eq133
    | (have j0 := eq133 (σ y)
       grind)
    | exact resolve eq133 eq2534080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq2534080
  have eq2813126 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq2811166
       have r₂ := eq2489087
       grind)
    | exact resolve eq2811166 eq2489087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489087 eq2811166
  have eq2814128 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2813126 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | (have r₁ := eq11 (σ y) (σ y)
       have r₂ := eq2813126
       grind)
    | exact resolve eq11 eq2813126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813126
  have eq2814129 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq2814128
  have eq2814754 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2814129 eq2532165
    | exact resolve eq2532165 eq2814129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532165 eq2814129
  have eq2814869 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq2814754
  have eq2815361 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq2814869 eq2168133
    | exact resolve eq2168133 eq2814869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168133 eq2814869
  have eq2815565 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2815361
  have eq2815889 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2815565
       have r₂ := eq2489544
       grind)
    | exact resolve eq2815565 eq2489544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815565
  have eq2816124 : (τ (σ x)) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2815889 eq154
    | exact resolve eq154 eq2815889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815889
  have eq2817466 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2816124 eq131
    | (have j0 := eq131 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq131 (τ (σ y)) (τ (σ x))
       have r₂ := eq2816124
       grind)
    | exact resolve eq131 eq2816124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2817574 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2817466
  have eq2817816 : (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq42 eq2817574
    | exact resolve eq2817574 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817574
  have eq2817817 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2817816
  have eq2855616 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2415939 eq2452088
    | exact resolve eq2452088 eq2415939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2452088
  have eq2855992 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2855616
  have eq2856275 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2855992 eq2454908
    | exact resolve eq2454908 eq2855992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454908 eq2855992
  have eq2856433 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2856275
  have eq2856751 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2856433 eq18399
    | (have r₁ := eq18399
       have r₂ := eq2856433
       grind)
    | exact resolve eq18399 eq2856433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18399 eq2856433
  have eq2857084 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2856751
  have eq2857085 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2857084
  have eq2857762 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2857085 eq154
    | exact resolve eq154 eq2857085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857085
  have eq2858245 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq2857762
       have r₂ := eq47
       grind)
    | exact resolve eq2857762 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857762
  have eq2858339 : (τ (σ x)) = (k (M.op x y) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2415939 eq2858245
    | exact resolve eq2858245 eq2415939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415939
  have eq2858703 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2858245 eq15
    | exact resolve eq15 eq2858245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858245
  have eq2859057 : (τ (σ x)) = (k (M.op x y) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2858339
  have eq2859086 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq2858703
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2858703
    | exact resolve eq2858703 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858703
  have eq2859154 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq2859086
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2859086
    | exact resolve eq2859086 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859086
  have eq2859238 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2859154 eq412
    | (have r₁ := eq412
       have r₂ := eq2859154
       grind)
    | exact resolve eq412 eq2859154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq2859923 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2859238
  have eq2859924 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2859923
  have eq2860943 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2859924 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2859924
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2859924
       grind)
    | exact resolve eq12 eq2859924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859924
  have eq2860945 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2860943
  have eq2861007 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq32 eq2860945
    | exact resolve eq2860945 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860945
  have eq2861008 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2861007
  have eq2861752 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2861008 eq2859154
    | exact resolve eq2859154 eq2861008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859154 eq2861008
  have eq2861910 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2861752
  have eq2862567 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2861910 eq1690499
    | exact resolve eq1690499 eq2861910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690499
  have eq2862604 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2861910 eq131
    | (have j0 := eq131 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq131 (σ x) (σ (M.op x y))
       have r₂ := eq2861910
       grind)
    | exact resolve eq131 eq2861910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2862723 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2862604
  have eq2862755 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2862567
  have eq2863000 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2862755
       have r₂ := eq1504085
       grind)
    | exact resolve eq2862755 eq1504085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862755
  have eq2895467 : (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2859057 eq2453952
    | (have r₁ := eq2453952
       have r₂ := eq2859057
       grind)
    | exact resolve eq2453952 eq2859057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453952
  have eq2895480 : (σ (τ (σ x))) = (k (σ (M.op x y)) (σ (τ (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2859057 eq15
    | exact resolve eq15 eq2859057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2895615 : (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2895467
  have eq2895616 : (τ (σ x)) = (M.op (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2895615
  have eq2895773 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq2895480
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2895480
    | exact resolve eq2895480 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895480
  have eq2895786 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq26 eq2895773
    | exact resolve eq2895773 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895773
  have eq2896145 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2895786 eq132
    | (have j0 := eq132 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq132 (σ x) (σ (M.op x y))
       have r₂ := eq2895786
       grind)
    | exact resolve eq132 eq2895786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895786
  have eq2896269 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2896145
  have eq2896556 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have j1 := eq131 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq2896269
       have r₂ := eq131 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq2896269 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq2896269
  have eq2896775 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2895616 eq12
    | (have j0 := eq12 (M.op x y) (τ (σ x))
       grind)
    | (have r₁ := eq12 (M.op x y) (τ (σ x))
       have r₂ := eq2895616
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2895616
       grind)
    | exact resolve eq12 eq2895616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895616
  have eq2896777 : (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq2896775
  have eq2954210 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2862723 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq11 (σ (M.op x y)) (σ x)
       have r₂ := eq2862723
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2862723
       grind)
    | exact resolve eq11 eq2862723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2954211 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2862723
  have eq2954212 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2954210
  have eq2954342 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2863000 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq2863000
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ x)
       have r₂ := eq2863000
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2863000
       grind)
    | exact resolve eq13 eq2863000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863000
  have eq2954347 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2954342
  have eq2954348 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2954347
  have eq2954360 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2954348
       have r₂ := eq1504085
       grind)
    | exact resolve eq2954348 eq1504085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504085 eq2954348
  have eq2955136 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2954212 eq2861910
    | exact resolve eq2861910 eq2954212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954212
  have eq2955308 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq2955136
  have eq2955576 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2955308
       have r₂ := eq2954211
       grind)
    | exact resolve eq2955308 eq2954211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954211 eq2955308
  have eq2955640 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2955576 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq2955576
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ x)
       have r₂ := eq2955576
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2955576
       grind)
    | exact resolve eq13 eq2955576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955576
  have eq2955644 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2955640
  have eq2955645 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2955644
  have eq2964534 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2955645
  have eq2969431 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2896556 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq11 (σ (M.op x y)) (σ x)
       have r₂ := eq2896556
       grind)
    | exact resolve eq11 eq2896556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2969432 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2896556
  have eq2969433 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq2969431
  have eq3045978 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2954360 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2954360
       grind)
    | exact resolve eq11 eq2954360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954360
  have eq3046008 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq3045978
       have r₂ := eq1503702
       grind)
    | exact resolve eq3045978 eq1503702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503702 eq3045978
  have eq3046041 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2861910 eq3046008
    | exact resolve eq3046008 eq2861910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861910 eq3046008
  have eq3046682 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq3046041
  have eq3046751 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq3046682
       have r₂ := eq2964534
       grind)
    | exact resolve eq3046682 eq2964534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964534 eq3046682
  have eq3216581 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2896777 eq2416449
    | exact resolve eq2416449 eq2896777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416449 eq2896777
  have eq3216587 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by grind
  clear eq3216581
  have eq3216706 : (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3216587 eq2859057
    | exact resolve eq2859057 eq3216587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859057 eq3216587
  have eq3216855 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq3216706
  have eq3217364 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq3216855 eq2969433
    | exact resolve eq2969433 eq3216855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969433
  have eq3217558 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq3217364
  have eq3217848 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq3217558
       have r₂ := eq2969432
       grind)
    | exact resolve eq3217558 eq2969432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969432 eq3217558
  have eq3225697 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq3217848 eq13
    | (have j0 := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ (M.op x y))
       have r₂ := eq3217848
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ x)
       have r₂ := eq3217848
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3217848
       grind)
    | exact resolve eq13 eq3217848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3217848
  have eq3225701 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq3225697
  have eq3225702 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq3225701
  have eq3264165 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq3225702 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq3225702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3264166 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq3225702
  have eq3327213 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq2419733 eq3264165
    | (have r₁ := eq3264165
       have r₂ := eq2419733
       grind)
    | exact resolve eq3264165 eq2419733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419733 eq3264165
  have eq3327231 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq3327213
  have eq3327232 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by grind
  clear eq3327231
  have eq3327257 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq3327232
       have r₂ := eq3264166
       grind)
    | exact resolve eq3327232 eq3264166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3264166 eq3327232
  have eq3327873 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq3327257 eq3216855
    | exact resolve eq3216855 eq3327257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216855 eq3327257
  have eq3328069 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3327873
  have eq3834986 : (τ (σ (σ (σ (σ (σ y)))))) = (k (τ (σ (σ (σ (σ (σ y)))))) (σ (σ (σ (σ x))))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq459918 eq53
    | exact resolve eq53 eq459918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459918
  have eq3835010 : (τ (σ (σ (σ (σ (σ y)))))) = (k (τ (σ (σ (σ (σ (σ y)))))) (σ (σ (σ (σ x))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq3834986
       have r₂ := eq2489544
       grind)
    | exact resolve eq3834986 eq2489544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489544 eq3834986
  have eq3835019 : (σ (σ (σ (σ y)))) = (k (σ (σ (σ (σ y)))) (σ (σ (σ (σ x))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3835010
       have i₂ := eq34 (σ (σ (σ sF5)))
       grind)
    | exact superpose eq34 eq3835010
    | exact resolve eq3835010 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835010
  have eq3835096 : (τ (σ (σ (σ (σ y))))) = (k (τ (σ (σ (σ (σ y))))) (σ (σ (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3835019 eq53
    | exact resolve eq53 eq3835019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835019
  have eq3835181 : (σ (σ (σ y))) = (k (σ (σ (σ y))) (σ (σ (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3835096
       have i₂ := eq34 (σ (σ sF5))
       grind)
    | exact superpose eq34 eq3835096
    | exact resolve eq3835096 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835096
  have eq3835324 : (τ (σ (σ (σ y)))) = (k (τ (σ (σ (σ y)))) (σ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3835181 eq53
    | exact resolve eq53 eq3835181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835181
  have eq3835498 : (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3835324
       have i₂ := eq34 (σ sF5)
       grind)
    | exact superpose eq34 eq3835324
    | exact resolve eq3835324 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835324
  have eq3835902 : (τ (σ (σ y))) = (k (τ (σ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3835498 eq53
    | exact resolve eq53 eq3835498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3835498
  have eq3836211 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3835902
       have i₂ := eq34 sF5
       grind)
    | exact superpose eq34 eq3835902
    | exact resolve eq3835902 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3835902
  have eq3996210 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2817817 eq11
    | (have j0 := eq11 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq11 (τ (σ x)) (τ (σ y))
       have r₂ := eq2817817
       grind)
    | exact resolve eq11 eq2817817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817817
  have eq3996212 : (τ (σ y)) = (k (τ (σ x)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3996210
  have eq4005578 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3996212 eq2816124
    | exact resolve eq2816124 eq3996212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816124 eq3996212
  have eq4005587 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq4005578
  have eq4005626 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq4005587 eq12
    | (have j0 := eq12 (τ (σ y)) (τ (σ x))
       grind)
    | (have r₁ := eq12 (τ (σ y)) (τ (σ x))
       have r₂ := eq4005587
       grind)
    | exact resolve eq12 eq4005587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005587
  have eq4005628 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq4005626
  have eq4005641 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq42 eq4005628
    | exact resolve eq4005628 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005628
  have eq4005768 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq4005641 eq2174427
    | exact resolve eq2174427 eq4005641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174427 eq4005641
  have eq4005860 : (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4005768
  have eq4007024 : (σ y) = (σ (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4005860 eq35
    | exact resolve eq35 eq4005860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005860
  have eq4008073 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4007024
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq4007024
    | exact resolve eq4007024 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4007024
  have eq4009293 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4008073 eq35
    | exact resolve eq35 eq4008073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4008073
  have eq4010568 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq4009293
    | exact resolve eq4009293 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4009293
  have eq4010569 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4010568
  have eq4012639 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4010569 eq35
    | exact resolve eq35 eq4010569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4010569
  have eq4014086 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq4012639
    | exact resolve eq4012639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012639
  have eq4014087 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4014086
  have eq4014551 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4014087 eq42
    | exact resolve eq42 eq4014087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq4015484 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4014087 eq122133
    | (have r₁ := eq122133
       have r₂ := eq4014087
       grind)
    | exact resolve eq122133 eq4014087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4017261 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4014087 eq3836211
    | exact resolve eq3836211 eq4014087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836211 eq4014087
  have eq4017480 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4017261
  have eq4019173 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4015484
  have eq4019174 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4019173
  have eq4020437 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4017480 eq154
    | exact resolve eq154 eq4017480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq4017480
  have eq4026506 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4020437 eq132
    | (have j0 := eq132 (τ (σ x)) (τ (σ x))
       grind)
    | (have r₁ := eq132 (τ (σ x)) (τ (σ x))
       have r₂ := eq4020437
       grind)
    | exact resolve eq132 eq4020437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq4020437
  have eq4026644 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4026506
  have eq4026645 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4026644
  have eq4028928 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4026645 eq4014551
    | exact resolve eq4014551 eq4026645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014551 eq4026645
  have eq4028931 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4028928
  have eq4030489 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4028931 eq35
    | exact resolve eq35 eq4028931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028931
  have eq4031417 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq4030489
    | exact resolve eq4030489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030489
  have eq4031418 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4031417
  have eq4033297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4031418 eq3046751
    | exact resolve eq3046751 eq4031418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046751
  have eq4033660 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4031418 eq3328069
    | exact resolve eq3328069 eq4031418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328069
  have eq4034123 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4031418
  have eq4034127 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4033660
  have eq4034152 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4033297
  have eq4034511 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4034127
       have r₂ := eq4034123
       grind)
    | exact resolve eq4034127 eq4034123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034127
  have eq4034868 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4034152
       have r₂ := eq4034123
       grind)
    | exact resolve eq4034152 eq4034123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034152
  have eq4035921 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32 eq4034511
    | exact resolve eq4034511 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034511
  have eq4035922 : (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4035921
  have eq4036079 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32 eq4034868
    | exact resolve eq4034868 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034868
  have eq4036080 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4036079
  have eq4038110 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4036080 eq33
    | exact resolve eq33 eq4036080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036080
  have eq4038126 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4038110
       have r₂ := eq4019174
       grind)
    | exact resolve eq4038110 eq4019174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4019174 eq4038110
  have eq4041017 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4035922 eq35
    | exact resolve eq35 eq4035922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035922
  have eq4042598 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq4041017
    | exact resolve eq4041017 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4041017
  have eq4042599 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4042598
  have eq4042830 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4042599 eq4038126
    | exact resolve eq4038126 eq4042599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4038126 eq4042599
  have eq4042831 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4042830
  have eq4042843 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4042831
       have r₂ := eq4034123
       grind)
    | exact resolve eq4042831 eq4034123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034123 eq4042831
  have eq4042920 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq4042843 eq36
    | exact resolve eq36 eq4042843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq4046594 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq4042920 eq47
    | (have r₁ := eq47
       have r₂ := eq4042920
       grind)
    | exact resolve eq47 eq4042920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq4042920
  have eq4048438 : (M.op x y) = (k (τ (σ y)) (M.op x y)) := by grind
  clear eq4046594
  have eq4049552 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq4048438 eq15
    | exact resolve eq15 eq4048438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4048438
  have eq4049665 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq4049552
    | exact resolve eq4049552 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4049552
  have eq4049674 : (σ x) = (k (σ (τ (σ y))) (σ x)) := by
    first
    | exact superpose eq4042843 eq4049665
    | exact resolve eq4049665 eq4042843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049665
  have eq4049675 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4049674
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq4049674
    | exact resolve eq4049674 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4049674
  have eq4049951 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4049675 eq73558
    | (have r₁ := eq73558
       have r₂ := eq4049675
       grind)
    | exact resolve eq73558 eq4049675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73558
  have eq4050498 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4049951
  have eq4050499 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4050498
  have eq4050614 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq4050499
       have r₂ := eq122133
       grind)
    | exact resolve eq4050499 eq122133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122133 eq4050499
  have eq4050655 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4042843 eq4050614
    | exact resolve eq4050614 eq4042843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050614
  have eq4050709 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4050655 eq33
    | exact resolve eq33 eq4050655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050655
  have eq4050781 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq4050709
       have r₂ := eq4042843
       grind)
    | exact resolve eq4050709 eq4042843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050709
  have eq4050790 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4050781 eq32
    | exact resolve eq32 eq4050781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq4053639 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4050781 eq4049675
    | exact resolve eq4049675 eq4050781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4049675 eq4050781
  have eq4055785 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4050790 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq4050790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050790
  have eq4055790 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4055785
  have eq4055792 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4053639 eq4055790
    | exact resolve eq4055790 eq4053639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4053639 eq4055790
  have eq4055793 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4055792
  have eq4055844 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4055793 eq33
    | exact resolve eq33 eq4055793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq4055793
  have eq4055878 : False := by grind
  exact eq4055878

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then Y else if m(Y,X) = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_x_pyx_x_pyx_y_pyx_y_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (σ X0) (σ X1))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq62 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq30
    | exact resolve eq30 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq110 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq62
    | exact resolve eq62 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
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
  have eq196 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq110
    | exact resolve eq110 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq226 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
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
  have eq380 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq196
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq505 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq226
    | exact resolve eq226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq704 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq380
    | exact resolve eq380 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq380
    | exact resolve eq380 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq834 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq505 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq505
    | exact resolve eq505 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq1424 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq704 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq704
    | exact resolve eq704 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq1503 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq720 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq720
    | exact resolve eq720 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq2025 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq834 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq834
    | exact resolve eq834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq2260 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2261 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq2264 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2265 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2266 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq2266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2270 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2261 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq2271 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2260
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq2260
    | exact resolve eq2260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2272 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq11 (σ y) (σ x)
       grind)
    | exact superpose eq11 eq2271
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq2271
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq2271 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2273 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2272
  have eq2280 : y ≠ y ∨ y = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2273
       grind)
    | exact superpose eq2273 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2273
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2273
       grind)
    | exact resolve eq13 eq2273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2281 : x ≠ y ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2273
  have eq2282 : y ≠ y ∨ y = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2280
  have eq2283 : x = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2282
  have eq2426 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq2283
       grind)
    | exact superpose eq2283 eq10
    | exact resolve eq10 eq2283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq2499 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2426
       grind)
    | exact superpose eq2426 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2426
       grind)
    | exact resolve eq13 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2501 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2499
  have eq2502 : x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2501
  have eq2576 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    grind
  have eq2578 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq2270 eq2576
    | (have j0 := eq2576 X0
       have j1 := eq2270 X0
       grind)
    | exact resolve eq2576 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq2582 : x ≠ x ∨ x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2502
       grind)
    | exact superpose eq2502 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2502
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2502
       grind)
    | exact resolve eq12 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2585 : x ≠ x ∨ x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2582
  have eq2586 : y = (k y x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2585
  have eq2732 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq2586
       grind)
    | exact superpose eq2586 eq10
    | exact resolve eq10 eq2586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586
  have eq2767 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1424 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1424
    | exact resolve eq1424 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq2805 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1503 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1503
    | exact resolve eq1503 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq2878 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2732
       grind)
    | exact superpose eq2732 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2732
       grind)
    | exact resolve eq12 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2879 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2732
       grind)
    | exact superpose eq2732 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq2880 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq2879
  have eq2881 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2878
  have eq2882 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2881
  have eq2886 : y = (M.op x x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2882
       have r₂ := eq2880
       grind)
    | exact resolve eq2882 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880 eq2882
  have eq2963 : y = (k x x) ∨ x = y ∨ x = y ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq2886
       grind)
    | exact superpose eq2886 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2968 : y = (k x x) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq2963
  have eq3047 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq2968
       grind)
    | exact superpose eq2968 eq10
    | exact resolve eq10 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968
  have eq3126 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq2264 X1 X0
       grind)
    | exact superpose eq2264 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq2264 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq2264 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq2264 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq2264 X1 X1
       grind)
    | exact resolve eq13 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3128 : (σ y) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq2264 (σ x) (σ y)
       grind)
    | exact superpose eq2264 eq2271
    | (have j1 := eq2264 x y
       grind)
    | exact resolve eq2271 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3133 : (σ y) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq3128
  have eq3135 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3126
  have eq3136 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3142 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2502 eq3133
    | exact resolve eq3133 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502 eq3133
  have eq3338 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2025 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2025
    | exact resolve eq2025 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq3380 : (σ x) = (σ y) ∨ (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2270 (σ x)
       have i₂ := eq3047
       grind)
    | exact superpose eq3047 eq2270
    | (have j0 := eq2270 (σ x)
       grind)
    | exact resolve eq2270 eq3047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3382 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  have eq3384 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11 (σ x) (σ x)
       have i₂ := eq3047
       grind)
    | exact superpose eq3047 eq11
    | exact resolve eq11 eq3047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3388 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3384
  have eq3392 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3388 eq3382
    | exact resolve eq3382 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq3393 : (σ x) = (σ y) ∨ (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2578 eq3380
    | (have j1 := eq2578 (σ x)
       grind)
    | exact resolve eq3380 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3380
  have eq3394 : (σ x) = (σ y) ∨ (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3393
  have eq3395 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3047 eq3392
    | exact resolve eq3392 eq3047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047 eq3392
  have eq3396 : x = y ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3395
  have eq3397 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3388 eq3394
    | exact resolve eq3394 eq3388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388 eq3394
  have eq3535 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3142
       have i₂ := eq3396
       grind)
    | exact superpose eq3396 eq3142
    | exact resolve eq3142 eq3396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396
  have eq3536 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3535
  have eq3537 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq3536
  have eq4272 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq3397
       grind)
    | exact superpose eq3397 eq2271
    | (have r₁ := eq2271
       have r₂ := eq3397
       grind)
    | exact resolve eq2271 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4279 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq4272
  have eq4571 : (M.op x x) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  have eq4576 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3537 eq4571
    | exact resolve eq4571 eq3537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537 eq4571
  have eq4912 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq4576
       grind)
    | exact superpose eq4576 eq10
    | exact resolve eq10 eq4576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4576
  have eq5569 : y ≠ y ∨ y = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq4279
       grind)
    | exact superpose eq4279 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4279
       grind)
    | exact resolve eq13 eq4279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq5571 : y ≠ y ∨ y = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq5569
  have eq5572 : x = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq5571
  have eq5737 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq5572
       grind)
    | exact superpose eq5572 eq10
    | exact resolve eq10 eq5572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq5738 : y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq5737
  have eq5913 : x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) := by grind
  have eq6105 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2767 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2767
    | exact resolve eq2767 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767
  have eq6275 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2805 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2805
    | exact resolve eq2805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805
  have eq6443 : x ≠ x ∨ x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq5913
       grind)
    | exact superpose eq5913 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq5913
       grind)
    | exact resolve eq12 eq5913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5913
  have eq6446 : x ≠ x ∨ x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq6443
  have eq6447 : x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq6446
  have eq6452 : y = (k y x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq5738 eq6447
    | exact resolve eq6447 eq5738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5738 eq6447
  have eq7154 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq6452
       grind)
    | exact superpose eq6452 eq10
    | exact resolve eq10 eq6452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6452
  have eq7156 : x = (k y x) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq7154
  have eq7302 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq7156
       grind)
    | exact superpose eq7156 eq10
    | exact resolve eq10 eq7156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7156
  have eq7303 : y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq7302
  have eq7694 : (M.op x y) = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq7303
  have eq8288 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq7694
       grind)
    | exact superpose eq7694 eq9
    | exact resolve eq9 eq7694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7694
  have eq8305 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8288
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq8288
    | exact resolve eq8288 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8288
  have eq8312 : x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8305
       have r₂ := eq3397
       grind)
    | exact resolve eq8305 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3397 eq8305
  have eq8496 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq8312
       grind)
    | exact superpose eq8312 eq9
    | exact resolve eq9 eq8312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8497 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq8312
       grind)
    | exact superpose eq8312 eq2271
    | exact resolve eq2271 eq8312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8506 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3142
       have i₂ := eq8312
       grind)
    | exact superpose eq8312 eq3142
    | (have r₁ := eq3142
       have r₂ := eq8312
       grind)
    | exact resolve eq3142 eq8312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8507 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq8506
  have eq8508 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq8507
  have eq8520 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq8497
  have eq8521 : (σ x) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8508 eq8520
    | exact resolve eq8520 eq8508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8520
  have eq8921 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  have eq8927 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8508 eq8921
    | exact resolve eq8921 eq8508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8508 eq8921
  have eq8928 : x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8927
       have r₂ := eq8521
       grind)
    | exact resolve eq8927 eq8521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8521 eq8927
  have eq9130 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8496
       have i₂ := eq8928
       grind)
    | exact superpose eq8928 eq8496
    | exact resolve eq8496 eq8928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8496
  have eq9131 : (M.op x x) = (k x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  have eq9132 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9130
  have eq9141 : x = (k x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8928 eq9131
    | exact resolve eq9131 eq8928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8928 eq9131
  have eq9291 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq9141
       grind)
    | exact superpose eq9141 eq10
    | exact resolve eq10 eq9141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9141
  have eq9452 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9132
       have i₂ := eq2267 (σ x)
       grind)
    | exact superpose eq2267 eq9132
    | (have j1 := eq2267 (σ x)
       grind)
    | (have r₁ := eq9132
       have r₂ := eq2267 (σ x)
       grind)
    | exact resolve eq9132 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132
  have eq9453 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) ≠ (k (σ x) (σ x)) := by grind
  clear eq9452
  have eq9464 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9453
       have r₂ := eq9291
       grind)
    | exact resolve eq9453 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9453
  have eq9667 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3338 x (σ y)
       have i₂ := eq9464
       grind)
    | exact superpose eq9464 eq3338
    | exact resolve eq3338 eq9464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9464
  have eq9672 : y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9667
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq9667
    | exact resolve eq9667 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9667
  have eq13193 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6105 X1 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq6105
    | exact resolve eq6105 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13259 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6105 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq6105
    | exact resolve eq6105 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6105
  have eq13337 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4912
       have i₂ := eq11 (σ x) (σ x)
       grind)
    | exact superpose eq11 eq4912
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq4912 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13341 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq4912
  have eq13346 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13337
  have eq13350 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq9291 eq13341
    | exact resolve eq13341 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13341
  have eq13351 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq13350
  have eq13354 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9291 eq13346
    | exact resolve eq13346 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13346
  have eq13355 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq13354
  have eq13356 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6275 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq6275
    | exact resolve eq6275 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6275
  have eq13816 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13355
       have i₂ := eq13351
       grind)
    | exact superpose eq13351 eq13355
    | exact resolve eq13355 eq13351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13351 eq13355
  have eq13828 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq13816
  have eq14056 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3338 x (σ y)
       have i₂ := eq13828
       grind)
    | exact superpose eq13828 eq3338
    | exact resolve eq3338 eq13828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq14060 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq13828
  have eq14064 : y = (k y x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14056
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq14056
    | exact resolve eq14056 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14056
  have eq21175 : y ≠ (k y x) ∨ x = (k y x) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq3136 y x
       grind)
    | exact superpose eq3136 eq9
    | (have j1 := eq3136 y x
       grind)
    | exact resolve eq9 eq3136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21242 : y ≠ y ∨ x = y ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21175
       have i₂ := eq9672
       grind)
    | exact superpose eq9672 eq21175
    | (have r₁ := eq21175
       have r₂ := eq9672
       grind)
    | exact resolve eq21175 eq9672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9672 eq21175
  have eq21245 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq21242
  have eq21941 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21245
       have i₂ := eq3136 (σ y) (σ x)
       grind)
    | exact superpose eq3136 eq21245
    | (have j1 := eq3136 (σ y) (σ x)
       grind)
    | (have r₁ := eq21245
       have r₂ := eq3136 (σ y) (σ x)
       grind)
    | exact resolve eq21245 eq3136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136 eq21245
  have eq21944 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq21941
  have eq21945 : x = y ∨ y = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq21944
  have eq21951 : y = (M.op x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq21945
       have r₂ := eq2886
       grind)
    | exact resolve eq21945 eq2886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2886 eq21945
  have eq22314 : y = (k x x) ∨ x = y ∨ x = y ∨ x = y ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq21951
       grind)
    | exact superpose eq21951 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq21951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21951
  have eq22319 : y = (k x x) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq22314
  have eq22681 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq22319
       grind)
    | exact superpose eq22319 eq10
    | exact resolve eq10 eq22319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22319
  have eq25661 : (σ x) = (σ y) ∨ (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2270 (σ x)
       have i₂ := eq22681
       grind)
    | exact superpose eq22681 eq2270
    | (have j0 := eq2270 (σ x)
       grind)
    | exact resolve eq2270 eq22681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq25666 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 (σ x) (σ x)
       have i₂ := eq22681
       grind)
    | exact superpose eq22681 eq11
    | exact resolve eq11 eq22681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22681
  have eq25671 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq25666
  have eq25675 : (σ x) = (σ y) ∨ (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq25661
  have eq25697 : (σ x) = (σ y) ∨ (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2578 eq25675
    | (have j1 := eq2578 (σ x)
       grind)
    | exact resolve eq25675 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25675
  have eq25698 : (σ x) = (σ y) ∨ (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq25697
  have eq25699 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq25671 eq25698
    | exact resolve eq25698 eq25671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25698
  have eq25700 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq8312 eq25699
    | exact resolve eq25699 eq8312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8312 eq25699
  have eq26080 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14060
       have i₂ := eq25671
       grind)
    | exact superpose eq25671 eq14060
    | (have r₁ := eq14060
       have r₂ := eq25671
       grind)
    | exact resolve eq14060 eq25671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25671
  have eq26105 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq26080
  have eq26106 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq26105
  have eq26615 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq25700
       grind)
    | exact superpose eq25700 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25700
       grind)
    | exact resolve eq13 eq25700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25700
  have eq26616 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26615
  have eq26617 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26616
  have eq27399 : (σ x) = (σ y) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2264 (σ x) (σ x)
       have i₂ := eq26617
       grind)
    | exact superpose eq26617 eq2264
    | (have j0 := eq2264 (σ x) (σ x)
       grind)
    | exact resolve eq2264 eq26617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264 eq26617
  have eq27406 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq27399
  have eq29385 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq18 x x
       have i₂ := eq26106
       grind)
    | exact superpose eq26106 eq18
    | exact resolve eq18 eq26106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29478 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2578 (σ x)
       have i₂ := eq26106
       grind)
    | exact superpose eq26106 eq2578
    | (have j0 := eq2578 (σ x)
       grind)
    | exact resolve eq2578 eq26106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26106
  have eq29484 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq29478
  have eq29491 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq9291 eq29484
    | exact resolve eq29484 eq9291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9291 eq29484
  have eq29584 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq29385
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq29385
    | exact resolve eq29385 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29385
  have eq29588 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq29491
       have r₂ := eq14060
       grind)
    | exact resolve eq29491 eq14060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29491
  have eq29681 : y = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq29584
       have r₂ := eq14060
       grind)
    | exact resolve eq29584 eq14060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29584
  have eq30179 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2578 x
       have i₂ := eq29681
       grind)
    | exact superpose eq29681 eq2578
    | (have j0 := eq2578 (σ x)
       grind)
    | exact resolve eq2578 eq29681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30182 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq29681
       grind)
    | exact superpose eq29681 eq10
    | exact resolve eq10 eq29681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29681
  have eq30197 : y = (M.op x y) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq14064 eq30179
    | exact resolve eq30179 eq14064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14064 eq30179
  have eq32989 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq30197
       grind)
    | exact superpose eq30197 eq9
    | exact resolve eq9 eq30197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30197
  have eq33017 : x = y ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq32989
       have r₂ := eq29588
       grind)
    | exact resolve eq32989 eq29588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29588 eq32989
  have eq33053 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30182
       have i₂ := eq33017
       grind)
    | exact superpose eq33017 eq30182
    | exact resolve eq30182 eq33017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33017
  have eq33059 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq33053
  have eq33126 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq27406
       have i₂ := eq33059
       grind)
    | exact superpose eq33059 eq27406
    | (have r₁ := eq27406
       have r₂ := eq33059
       grind)
    | exact resolve eq27406 eq33059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27406
  have eq33229 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13259 x (σ x)
       have i₂ := eq33059
       grind)
    | exact superpose eq33059 eq13259
    | exact resolve eq13259 eq33059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13259
  have eq33230 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2265 (σ x) (σ x)
       have i₂ := eq33059
       grind)
    | exact superpose eq33059 eq2265
    | (have j0 := eq2265 (σ x) (σ x)
       grind)
    | (have r₁ := eq2265 (σ x) (σ x)
       have r₂ := eq33059
       grind)
    | (have r₁ := eq2265 (σ x) (σ y)
       have r₂ := eq33059
       grind)
    | exact resolve eq2265 eq33059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33059
  have eq33233 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq33230
  have eq33234 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq33233
  have eq33235 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq33126
  have eq33236 : x = y ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq33235
  have eq33244 : x = (k x x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq33229
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq33229
    | exact resolve eq33229 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33229
  have eq33367 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2265 x x
       have i₂ := eq33244
       grind)
    | exact superpose eq33244 eq2265
    | (have j0 := eq2265 x x
       grind)
    | (have r₁ := eq2265 x x
       have r₂ := eq33244
       grind)
    | (have r₁ := eq2265 (σ x) (σ y)
       have r₂ := eq33244
       grind)
    | exact resolve eq2265 eq33244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33244
  have eq33370 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq33367
  have eq33371 : x = (M.op x x) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq33370
  have eq33473 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq33236
       grind)
    | exact superpose eq33236 eq9
    | exact resolve eq9 eq33236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33236
  have eq33544 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33234 eq33473
    | exact resolve eq33473 eq33234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33234 eq33473
  have eq33545 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33371 eq33544
    | exact resolve eq33544 eq33371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33371 eq33544
  have eq33546 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq33545
  have eq33602 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13193 y (σ x)
       have i₂ := eq33546
       grind)
    | exact superpose eq33546 eq13193
    | exact resolve eq13193 eq33546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13193
  have eq33652 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2265 (σ x) (σ y)
       have i₂ := eq33546
       grind)
    | exact superpose eq33546 eq2265
    | (have j0 := eq2265 (σ x) (σ y)
       grind)
    | (have r₁ := eq2265 (σ x) (σ y)
       have r₂ := eq33546
       grind)
    | exact resolve eq2265 eq33546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33655 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq33652
  have eq33707 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33602
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq33602
    | exact resolve eq33602 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33602
  have eq33819 : x ≠ x ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2265 x y
       have i₂ := eq33707
       grind)
    | exact superpose eq33707 eq2265
    | (have j0 := eq2265 x y
       grind)
    | (have r₁ := eq2265 x y
       have r₂ := eq33707
       grind)
    | exact resolve eq2265 eq33707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33822 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq33819
  have eq34594 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq33822
  have eq34611 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33707 eq34594
    | exact resolve eq34594 eq33707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34594
  have eq34612 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq34611
  have eq34621 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq34612
       grind)
    | exact superpose eq34612 eq9
    | exact resolve eq9 eq34612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34612
  have eq34710 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq13356 y (σ x)
       have i₂ := eq30182
       grind)
    | exact superpose eq30182 eq13356
    | exact resolve eq13356 eq30182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13356
  have eq35095 : x = (k y x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq34710
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq34710
    | exact resolve eq34710 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34710
  have eq35119 : x = (k y x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33707 eq35095
    | exact resolve eq35095 eq33707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35095
  have eq35120 : x = (k y x) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq35119
  have eq35137 : x ≠ x ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2265 x y
       have i₂ := eq35120
       grind)
    | exact superpose eq35120 eq2265
    | (have j0 := eq2265 x y
       grind)
    | (have r₁ := eq2265 x y
       have r₂ := eq35120
       grind)
    | (have r₁ := eq2265 (σ x) (σ x)
       have r₂ := eq35120
       grind)
    | exact resolve eq2265 eq35120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35120
  have eq35140 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq35137
  have eq39042 : x ≠ y ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq35140
  have eq53301 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34621
       have i₂ := eq33655
       grind)
    | exact superpose eq33655 eq34621
    | (have r₁ := eq34621
       have r₂ := eq33655
       grind)
    | exact resolve eq34621 eq33655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33655 eq34621
  have eq53310 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq53301
  have eq53311 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq53310
  have eq53630 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq53311
       grind)
    | exact superpose eq53311 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq53311
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq53311
       grind)
    | exact resolve eq12 eq53311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53311
  have eq53633 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq53630
  have eq53634 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq53633
  have eq53658 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33546 eq53634
    | exact resolve eq53634 eq33546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53634
  have eq53659 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq53658
  have eq53687 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq53659
       grind)
    | exact superpose eq53659 eq9
    | exact resolve eq9 eq53659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53694 : x ≠ x ∨ x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq53659
       grind)
    | exact superpose eq53659 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq53659
       grind)
    | exact resolve eq12 eq53659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53659
  have eq53696 : x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq53694
  have eq53710 : x = y ∨ y = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33707 eq53696
    | exact resolve eq53696 eq33707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53696
  have eq53711 : y = (M.op x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq53710
  have eq54038 : y = (k x x) ∨ x = y ∨ x = y ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq53711
       grind)
    | exact superpose eq53711 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq53711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53711
  have eq54043 : y = (k x x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq54038
  have eq54369 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq54043
       grind)
    | exact superpose eq54043 eq10
    | exact resolve eq10 eq54043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54043
  have eq55002 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 (σ x) (σ x)
       have i₂ := eq54369
       grind)
    | exact superpose eq54369 eq11
    | exact resolve eq11 eq54369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54369
  have eq55007 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq55002
  have eq55035 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq55007
       grind)
    | exact superpose eq55007 eq9
    | exact resolve eq9 eq55007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55036 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq55007
       grind)
    | exact superpose eq55007 eq2271
    | exact resolve eq2271 eq55007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55045 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3142
       have i₂ := eq55007
       grind)
    | exact superpose eq55007 eq3142
    | (have r₁ := eq3142
       have r₂ := eq55007
       grind)
    | exact resolve eq3142 eq55007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142
  have eq55066 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30182
       have i₂ := eq55007
       grind)
    | exact superpose eq55007 eq30182
    | exact resolve eq30182 eq55007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30182
  have eq55075 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39042
       have i₂ := eq55007
       grind)
    | exact superpose eq55007 eq39042
    | (have r₁ := eq39042
       have r₂ := eq55007
       grind)
    | exact resolve eq39042 eq55007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39042
  have eq55080 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq55075
  have eq55081 : x = (M.op x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq55080
  have eq55091 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq55066
  have eq55117 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq55045
  have eq55118 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq55117
  have eq55130 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq55036
  have eq55131 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq55081 eq55130
    | exact resolve eq55130 eq55081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55081 eq55130
  have eq55132 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq55131
       have r₂ := eq55118
       grind)
    | exact resolve eq55131 eq55118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55118 eq55131
  have eq55192 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq55035
       have i₂ := eq55132
       grind)
    | exact superpose eq55132 eq55035
    | exact resolve eq55035 eq55132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55035 eq55132
  have eq55194 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by grind
  clear eq55192
  have eq55287 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq18 x x
       have i₂ := eq55091
       grind)
    | exact superpose eq55091 eq18
    | exact resolve eq18 eq55091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55567 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq55287
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq55287
    | exact resolve eq55287 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55287
  have eq55717 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2578 x
       have i₂ := eq55567
       grind)
    | exact superpose eq55567 eq2578
    | (have j0 := eq2578 (σ x)
       grind)
    | exact resolve eq2578 eq55567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55567
  have eq55737 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33707 eq55717
    | exact resolve eq55717 eq33707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55717
  have eq55740 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq55007 eq55737
    | exact resolve eq55737 eq55007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55007 eq55737
  have eq55741 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq55740
  have eq55754 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq55741
       grind)
    | exact superpose eq55741 eq9
    | exact resolve eq9 eq55741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55761 : x ≠ x ∨ x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq55741
       grind)
    | exact superpose eq55741 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq55741
       grind)
    | exact resolve eq12 eq55741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55741
  have eq55763 : x ≠ x ∨ x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq55761
  have eq55764 : x = y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq55763
  have eq55782 : x = y ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33707 eq55764
    | exact resolve eq55764 eq33707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33707 eq55764
  have eq55783 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq55782
  have eq56734 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq55194
       have i₂ := eq2267 (σ x)
       grind)
    | exact superpose eq2267 eq55194
    | (have j1 := eq2267 (σ x)
       grind)
    | (have r₁ := eq55194
       have r₂ := eq2267 (σ x)
       grind)
    | exact resolve eq55194 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267 eq55194
  have eq56741 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) := by grind
  clear eq56734
  have eq56759 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq56741
       have r₂ := eq55091
       grind)
    | exact resolve eq56741 eq55091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55091 eq56741
  have eq56780 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18 x x
       have i₂ := eq56759
       grind)
    | exact superpose eq56759 eq18
    | exact resolve eq18 eq56759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq56915 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2578 (σ x)
       have i₂ := eq56759
       grind)
    | exact superpose eq56759 eq2578
    | exact resolve eq2578 eq56759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578 eq56759
  have eq56920 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq56915
  have eq56928 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33546 eq56920
    | exact resolve eq56920 eq33546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33546 eq56920
  have eq57063 : y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56780
       have i₂ := eq16 y
       grind)
    | exact superpose eq16 eq56780
    | exact resolve eq56780 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56780
  have eq57215 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2265 x x
       have i₂ := eq57063
       grind)
    | exact superpose eq57063 eq2265
    | (have j0 := eq2265 x x
       grind)
    | exact resolve eq2265 eq57063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57063
  have eq57218 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq57215
  have eq57232 : x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq55754 eq57218
  have eq57259 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55783
       have i₂ := eq57232
       grind)
    | exact superpose eq57232 eq55783
    | exact resolve eq55783 eq57232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55783
  have eq57261 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq57259
  have eq57287 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq57261
       grind)
    | exact superpose eq57261 eq9
    | exact resolve eq9 eq57261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57404 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq57232 eq57287
    | exact resolve eq57287 eq57232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57232 eq57287
  have eq57426 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53687
       have i₂ := eq56928
       grind)
    | exact superpose eq56928 eq53687
    | (have r₁ := eq53687
       have r₂ := eq56928
       grind)
    | exact resolve eq53687 eq56928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53687 eq56928
  have eq57434 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq57426
  have eq57435 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq57434
  have eq57456 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq57261 eq57435
    | exact resolve eq57435 eq57261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57261 eq57435
  have eq57462 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq57456
       have r₂ := eq57404
       grind)
    | exact resolve eq57456 eq57404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57404 eq57456
  have eq57470 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq14060
       have r₂ := eq57462
       grind)
    | exact resolve eq14060 eq57462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14060
  have eq57476 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq57470
       have i₂ := eq57462
       grind)
    | exact superpose eq57462 eq57470
    | exact resolve eq57470 eq57462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57470
  have eq57477 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq57476
  have eq57492 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2271
       have i₂ := eq57462
       grind)
    | exact superpose eq57462 eq2271
    | exact resolve eq2271 eq57462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq57521 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq57462
       grind)
    | exact superpose eq57462 eq16
    | exact resolve eq16 eq57462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57842 : x = y := by
    first
    | (have i₁ := eq57521
       have i₂ := eq16 x
       grind)
    | exact superpose eq16 eq57521
    | exact resolve eq57521 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57521
  have eq57844 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq57492
       have i₂ := eq57477
       grind)
    | exact superpose eq57477 eq57492
    | exact resolve eq57492 eq57477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57477 eq57492
  have eq57845 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq2281
       have r₂ := eq57842
       grind)
    | exact resolve eq2281 eq57842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq57856 : x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq57844
       have i₂ := eq57842
       grind)
    | exact superpose eq57842 eq57844
    | exact resolve eq57844 eq57842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57844
  have eq57857 : x = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57845
       have i₂ := eq57842
       grind)
    | exact superpose eq57842 eq57845
    | exact resolve eq57845 eq57842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57845
  have eq57866 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq57856
       have i₂ := eq57842
       grind)
    | exact superpose eq57842 eq57856
    | exact resolve eq57856 eq57842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57856
  have eq57867 : x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq57866
  have eq57868 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57857
       have i₂ := eq57842
       grind)
    | exact superpose eq57842 eq57857
    | exact resolve eq57857 eq57842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57857
  have eq57869 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq57868
  have eq57881 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57867
       have i₂ := eq57842
       grind)
    | exact superpose eq57842 eq57867
    | exact resolve eq57867 eq57842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57867
  have eq57882 : x = (M.op x x) ∨ (σ x) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq57881
  have eq57883 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57869
       have i₂ := eq57462
       grind)
    | exact superpose eq57462 eq57869
    | exact resolve eq57869 eq57462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57869
  have eq57893 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57883
       have i₂ := eq57462
       grind)
    | exact superpose eq57462 eq57883
    | exact resolve eq57883 eq57462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57883
  have eq57894 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq57893
  have eq57896 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq57894
       have i₂ := eq57462
       grind)
    | exact superpose eq57462 eq57894
    | exact resolve eq57894 eq57462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57462 eq57894
  have eq57897 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq57896
  have eq57898 : x = (M.op x x) := by
    first
    | (have r₁ := eq57897
       have r₂ := eq57882
       grind)
    | exact resolve eq57897 eq57882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57882 eq57897
  have eq57899 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq57842
       grind)
    | exact superpose eq57842 eq9
    | exact resolve eq9 eq57842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57842
  have eq57972 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57899
       have i₂ := eq57898
       grind)
    | exact superpose eq57898 eq57899
    | exact resolve eq57899 eq57898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57899
  have eq58017 : (M.op x x) = (k x x) := by grind
  have eq58037 : x = (k x x) := by
    first
    | (have i₁ := eq58017
       have i₂ := eq57898
       grind)
    | exact superpose eq57898 eq58017
    | exact resolve eq58017 eq57898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57898 eq58017
  have eq58078 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq23 x x
       have i₂ := eq58037
       grind)
    | exact superpose eq58037 eq23
    | exact resolve eq23 eq58037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq58037
  have eq58897 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2265 (σ x) (σ x)
       have i₂ := eq58078
       grind)
    | exact superpose eq58078 eq2265
    | (have j0 := eq2265 (σ x) (σ x)
       grind)
    | (have r₁ := eq2265 (σ x) (σ x)
       have r₂ := eq58078
       grind)
    | exact resolve eq2265 eq58078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265 eq58078
  have eq58900 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq58897
  have eq58901 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq58900
  have eq58906 : False := by grind
  exact eq58906

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_pyx_pyx_pyy_pyx_pyy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  clear eq24 eq38
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
  clear eq40 eq41
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
  have eq73 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq73 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq73 x
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq92 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq13
    | (have j0 := eq13 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq13 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq74 sF4
       grind)
    | exact superpose eq74 eq93
    | exact resolve eq93 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq96 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq92
       have i₂ := eq74 (τ sF4)
       grind)
    | exact superpose eq74 eq92
    | exact resolve eq92 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq98 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq74 sF5
       grind)
    | exact superpose eq74 eq95
    | exact resolve eq95 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq96
       have i₂ := eq74 (τ sF5)
       grind)
    | exact superpose eq74 eq96
    | exact resolve eq96 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq101 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq74 sF4
       grind)
    | exact superpose eq74 eq98
    | exact resolve eq98 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op (τ (σ y)) (τ (σ y))) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq99
       have i₂ := eq74 (τ sF4)
       grind)
    | exact superpose eq74 eq99
    | exact resolve eq99 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq104 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq74 sF5
       grind)
    | exact superpose eq74 eq101
    | exact resolve eq101 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq102
       have i₂ := eq74 (τ sF5)
       grind)
    | exact superpose eq74 eq102
    | exact resolve eq102 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq121 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq138 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | (have j0 := eq14 x (τ (σ x))
       grind)
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq158 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq151 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq151 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq151 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq159 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq74 sF5
       grind)
    | exact superpose eq74 eq140
    | exact resolve eq140 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq161 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq74 (τ sF5)
       grind)
    | exact superpose eq74 eq138
    | exact resolve eq138 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq168 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq158
    | (have j0 := eq158 X0 X1
       grind)
    | (have r₁ := eq158 X0 X0
       have r₂ := eq74 X0
       grind)
    | exact resolve eq158 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq169 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq159
       have i₂ := eq74 sF4
       grind)
    | exact superpose eq74 eq159
    | exact resolve eq159 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq171 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq161
       have i₂ := eq74 (τ sF4)
       grind)
    | exact superpose eq74 eq161
    | exact resolve eq161 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq178 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (k X0 X1) ≠ (k X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq168
    | (have j0 := eq168 X0 X1
       grind)
    | exact resolve eq168 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq179 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq169
       have i₂ := eq74 sF4
       grind)
    | exact superpose eq74 eq169
    | exact resolve eq169 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq181 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq171
       have i₂ := eq74 (τ sF4)
       grind)
    | exact superpose eq74 eq171
    | exact resolve eq171 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq188 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k X0 X1) = (k X0 X0) ∨ (k X0 X1) ≠ (k X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq178
    | (have j0 := eq178 X0 X1
       grind)
    | exact resolve eq178 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq194 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq254 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | exact resolve eq11 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq254
    | (have j0 := eq254 X0 X1
       grind)
    | (have r₁ := eq254 X0 X0
       have r₂ := eq74 X0
       grind)
    | exact resolve eq254 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq258 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq256 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq256
    | (have j0 := eq256 X0 X1
       grind)
    | (have r₁ := eq256 X0 X0
       have r₂ := eq74 X0
       grind)
    | exact resolve eq256 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq256
  have eq326 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq179 eq33
    | exact resolve eq33 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq181 eq15
    | exact resolve eq15 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq456
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq456
    | exact resolve eq456 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq467 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq458 eq15
    | exact resolve eq15 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq467
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq467
    | exact resolve eq467 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq475 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq472
    | exact resolve eq472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq478 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq475 eq15
    | exact resolve eq15 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq478
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq478
    | exact resolve eq478 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq480 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq479
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq479
    | exact resolve eq479 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq481 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq480
    | exact resolve eq480 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq492 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq481 eq15
    | exact resolve eq15 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq492
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq492
    | exact resolve eq492 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq500 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq497
    | exact resolve eq497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq503 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq500 eq121
    | exact resolve eq121 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq539 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq503 eq255
    | (have j0 := eq255 (τ (σ x)) X0
       grind)
    | (have r₁ := eq255 (τ (σ x)) x
       have r₂ := eq503
       grind)
    | exact resolve eq255 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq541 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq181 eq255
    | (have j0 := eq255 (τ (σ x)) X0
       grind)
    | (have r₁ := eq255 (τ (σ x)) x
       have r₂ := eq181
       grind)
    | exact resolve eq255 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq547 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | (have j0 := eq541 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq548 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq571 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq258
    | (have j0 := eq258 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq258 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq258
    | (have j0 := eq258 (σ y) (σ x)
       grind)
    | exact resolve eq258 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq665 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq548 eq42
    | exact resolve eq42 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq700 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq665 eq15
    | exact resolve eq15 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq701 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq700
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq700
    | exact resolve eq700 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq702 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq701
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq701
    | exact resolve eq701 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq703 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq702
    | exact resolve eq702 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq704 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq703
  have eq714 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq704
  have eq733 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq458 eq571
    | (have r₁ := eq571
       have r₂ := eq458
       grind)
    | exact resolve eq571 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq734 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq733
  have eq735 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq481 eq105
    | (have r₁ := eq105
       have r₂ := eq481
       grind)
    | exact resolve eq105 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq736 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq735
  have eq774 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq179 eq573
    | (have r₁ := eq573
       have r₂ := eq179
       grind)
    | exact resolve eq573 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq775 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq774
  have eq776 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq775
  have eq839 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq547 eq42
    | exact resolve eq42 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq849 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq839
  have eq854 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq849 eq571
    | (have r₁ := eq571
       have r₂ := eq849
       grind)
    | exact resolve eq571 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq868 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq854
  have eq1032 : (k (τ (σ y)) (τ (σ x))) = (τ (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq776 eq121
    | exact resolve eq121 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq1039 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1032
       have i₂ := eq121 sF4 sF4
       grind)
    | exact superpose eq121 eq1032
    | exact resolve eq1032 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1107 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1039 eq475
    | exact resolve eq475 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq1108 : (k (τ (σ x)) (τ (σ x))) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1039 eq194
    | (have j0 := eq194 (τ (σ x)) (τ (σ x))
       grind)
    | (have r₁ := eq194 (τ (σ y)) (τ (σ x))
       have r₂ := eq1039
       grind)
    | exact resolve eq194 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1113 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1108
  have eq1114 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1107
  have eq1121 : (k (τ (σ x)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42 eq1113
    | exact resolve eq1113 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1122 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1114
       have r₂ := eq326
       grind)
    | exact resolve eq1114 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1296 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1122 eq15
    | exact resolve eq15 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1302 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1296
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1296
    | exact resolve eq1296 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296
  have eq1305 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1302
    | exact resolve eq1302 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1312 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq734 eq15
    | exact resolve eq15 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1321 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq1312
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1312
    | exact resolve eq1312 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1326 : (k (σ y) (σ x)) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq1321
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1321
    | exact resolve eq1321 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1328 : (k (σ y) (σ x)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq1326
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq1326
    | exact resolve eq1326 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1329 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq1328
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1328
    | exact resolve eq1328 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1333 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1305 eq33
    | exact resolve eq33 eq1305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1305
  have eq2403 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq868 eq15
    | exact resolve eq15 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq2413 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2403
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2403
    | exact resolve eq2403 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq2418 : (k (σ y) (σ x)) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2413
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq2413
    | exact resolve eq2413 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2420 : (k (σ y) (σ x)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2418
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq2418
    | exact resolve eq2418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2421 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2420
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2420
    | exact resolve eq2420 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq2459 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq1329 eq15
    | exact resolve eq15 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq2464 : (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2459
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq2459
    | exact resolve eq2459 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq2465 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq2464
  have eq3119 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1121
  have eq3129 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3119
       have r₂ := eq1122
       grind)
    | exact resolve eq3119 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122 eq3119
  have eq4204 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2465 eq15
    | exact resolve eq15 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465
  have eq4213 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4204
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq4204
    | exact resolve eq4204 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4214 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4213
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq4213
    | exact resolve eq4213 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213
  have eq4215 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4214
    | exact resolve eq4214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214
  have eq4219 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4215 eq105
    | (have r₁ := eq105
       have r₂ := eq4215
       grind)
    | exact resolve eq105 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq4226 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4215 eq15
    | exact resolve eq15 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4215
  have eq4237 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq4219
  have eq4242 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4226
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq4226
    | exact resolve eq4226 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4243 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4242
    | exact resolve eq4242 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4242
  have eq4262 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4243 eq1334
    | (have r₁ := eq1334
       have r₂ := eq4243
       grind)
    | exact resolve eq1334 eq4243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq4266 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4243 eq194
    | (have j0 := eq194 (σ x) (σ x)
       grind)
    | (have r₁ := eq194 (σ y) (σ x)
       have r₂ := eq4243
       grind)
    | exact resolve eq194 eq4243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq4243
  have eq4269 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq4266
  have eq4270 : (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq4269
  have eq4273 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq4262
  have eq4274 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq4273
  have eq4275 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq4270
       have r₂ := eq714
       grind)
    | exact resolve eq4270 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270
  have eq4279 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq4274
       have r₂ := eq1333
       grind)
    | exact resolve eq4274 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333 eq4274
  have eq4280 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq4275
    | exact resolve eq4275 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4275
  have eq4287 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4279 eq104
    | (have r₁ := eq104
       have r₂ := eq4279
       grind)
    | exact resolve eq104 eq4279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq4289 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4279 eq573
    | exact resolve eq573 eq4279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4290 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq4289
  have eq4292 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq4287
  have eq4293 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq4292
  have eq4307 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4280 eq4279
    | exact resolve eq4279 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq4308 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq4307
  have eq4318 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq4308
       have r₂ := eq714
       grind)
    | exact resolve eq4308 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq4308
  have eq4328 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4318 eq121
    | exact resolve eq121 eq4318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4318
  have eq4369 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq2421 eq255
    | (have j0 := eq255 (τ (σ x)) X0
       grind)
    | (have r₁ := eq255 (τ (σ x)) x
       have r₂ := eq2421
       grind)
    | exact resolve eq255 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq4376 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    intro X0
    first
    | (have j0 := eq4369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4369
  have eq4412 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq4328 eq255
    | (have j0 := eq255 (τ (σ x)) X0
       grind)
    | (have r₁ := eq255 (τ (σ x)) x
       have r₂ := eq4328
       grind)
    | exact resolve eq255 eq4328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4328
  have eq4419 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4412 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4412
  have eq4709 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4419 eq42
    | exact resolve eq42 eq4419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq4811 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4709 eq15
    | exact resolve eq15 eq4709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4709
  have eq4819 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4811
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq4811
    | exact resolve eq4811 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4811
  have eq4820 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq4819
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq4819
    | exact resolve eq4819 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4819
  have eq4821 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq4820
    | exact resolve eq4820 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4820
  have eq4822 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq4821
  have eq4824 : (M.op x y) = (τ (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4822 eq36
    | exact resolve eq36 eq4822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4836 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  have eq4845 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4824
       have i₂ := eq121 sF4 sF5
       grind)
    | exact superpose eq121 eq4824
    | exact resolve eq4824 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824
  have eq5490 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3129 eq15
    | exact resolve eq15 eq3129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq5500 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5490
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq5490
    | exact resolve eq5490 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5490
  have eq5501 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq5500
  have eq8045 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ y)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq736 eq15
    | exact resolve eq15 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq8077 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq8045
       have i₂ := eq15 (τ sF5) (τ sF4)
       grind)
    | exact superpose eq15 eq8045
    | exact resolve eq8045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8080 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq8077
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq8077
    | exact resolve eq8077 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8077
  have eq8081 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq8080
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq8080
    | exact resolve eq8080 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8080
  have eq12272 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq5501 eq15
    | exact resolve eq15 eq5501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5501
  have eq12297 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12272
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq12272
    | exact resolve eq12272 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12272
  have eq12299 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12297
    | exact resolve eq12297 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12297
  have eq12300 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq12299
       have r₂ := eq326
       grind)
    | exact resolve eq12299 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq12299
  have eq12303 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq12300 eq33
    | exact resolve eq33 eq12300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12305 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq12300 eq573
    | exact resolve eq573 eq12300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq12308 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq12300
  have eq12311 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq12305
  have eq12316 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq12311
       have r₂ := eq12308
       grind)
    | exact resolve eq12311 eq12308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12311
  have eq25263 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq4376 eq42
    | exact resolve eq42 eq4376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4376
  have eq25273 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by grind
  clear eq25263
  have eq25300 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq25273 eq15
    | exact resolve eq15 eq25273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25273
  have eq25317 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq25300
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq25300
    | exact resolve eq25300 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25300
  have eq25318 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq25317
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq25317
    | exact resolve eq25317 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25317
  have eq25319 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq25318
    | exact resolve eq25318 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25318
  have eq27803 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq8081 eq15
    | exact resolve eq15 eq8081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8081
  have eq27835 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq27803
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq27803
    | exact resolve eq27803 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27803
  have eq27836 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq27835
    | exact resolve eq27835 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27835
  have eq27837 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq27836
  have eq40295 : (k (τ (σ y)) (τ (σ y))) = (τ (k (σ y) (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4293 eq121
    | exact resolve eq121 eq4293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4293
  have eq40339 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40295
       have i₂ := eq121 sF4 sF5
       grind)
    | exact superpose eq121 eq40295
    | exact resolve eq40295 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40295
  have eq121597 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27837 eq12316
    | (have r₁ := eq12316
       have r₂ := eq27837
       grind)
    | exact resolve eq12316 eq27837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12316 eq27837
  have eq121627 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq121597
  have eq121628 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq121627
  have eq121656 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq121628
       have r₂ := eq12303
       grind)
    | exact resolve eq121628 eq12303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121628
  have eq121661 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq4280 eq121656
    | exact resolve eq121656 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq121664 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq121656 eq33
    | exact resolve eq33 eq121656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121656
  have eq121676 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq121661
  have eq121682 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq121676
       have r₂ := eq121664
       grind)
    | exact resolve eq121676 eq121664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121664 eq121676
  have eq128160 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (σ (k (τ (σ y)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4237 eq15
    | exact resolve eq15 eq4237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4237
  have eq128224 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq128160
       have i₂ := eq15 (τ sF5) (τ sF4)
       grind)
    | exact superpose eq15 eq128160
    | exact resolve eq128160 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128160
  have eq128235 : (k (σ (τ (σ y))) (σ (τ (σ y)))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq128224
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq128224
    | exact resolve eq128224 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128224
  have eq128238 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq128235
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq128235
    | exact resolve eq128235 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128235
  have eq204964 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq128238 eq571
    | (have r₁ := eq571
       have r₂ := eq128238
       grind)
    | exact resolve eq571 eq128238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128238
  have eq205049 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq204964
  have eq401035 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq205049 eq15
    | exact resolve eq15 eq205049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205049
  have eq401161 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq401035
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq401035
    | exact resolve eq401035 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401035
  have eq401400 : (k (σ y) (σ x)) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq401161
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq401161
    | exact resolve eq401161 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401161
  have eq401403 : (k (σ y) (σ x)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq401400
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq401400
    | exact resolve eq401400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401400
  have eq401404 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq401403
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq401403
    | exact resolve eq401403 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401403
  have eq401405 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq401404
  have eq520991 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq40339 eq571
    | exact resolve eq571 eq40339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq40339
  have eq521169 : (k (τ (σ y)) (τ (σ x))) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq520991
       have r₂ := eq4845
       grind)
    | exact resolve eq520991 eq4845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4845 eq520991
  have eq524745 : (M.op x y) = (τ (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq401405 eq25319
    | exact resolve eq25319 eq401405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25319 eq401405
  have eq524799 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq524745
  have eq601639 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq524799 eq121682
    | exact resolve eq121682 eq524799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121682 eq524799
  have eq601714 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq601639
  have eq601901 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq601714 eq12308
    | (have r₁ := eq12308
       have r₂ := eq601714
       grind)
    | exact resolve eq12308 eq601714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12308 eq601714
  have eq602052 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq601901
  have eq602053 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq602052
  have eq602080 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq602053
       have r₂ := eq12303
       grind)
    | exact resolve eq602053 eq12303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12303 eq602053
  have eq602106 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq602080 eq33
    | exact resolve eq33 eq602080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602610 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4822 eq602106
    | (have r₁ := eq602106
       have r₂ := eq4822
       grind)
    | exact resolve eq602106 eq4822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602613 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq602610
       have r₂ := eq602106
       grind)
    | exact resolve eq602610 eq602106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602610
  have eq639689 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq521169 eq15
    | exact resolve eq15 eq521169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521169
  have eq639954 : (σ (k (τ (σ x)) (τ (σ x)))) = (k (σ (τ (σ y))) (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq639689
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq639689
    | exact resolve eq639689 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639689
  have eq639959 : (k (σ y) (σ x)) = (σ (k (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq639954
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq639954
    | exact resolve eq639954 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639954
  have eq639962 : (k (σ y) (σ x)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq639959
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq639959
    | exact resolve eq639959 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639959
  have eq639963 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq639962
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq639962
    | exact resolve eq639962 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639962
  have eq639964 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq639963
       have r₂ := eq4290
       grind)
    | exact resolve eq639963 eq4290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4290 eq639963
  have eq639965 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq639964
       have r₂ := eq4836
       grind)
    | exact resolve eq639964 eq4836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4836 eq639964
  have eq640021 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq639965 eq15
    | exact resolve eq15 eq639965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639965
  have eq640122 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq640021
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq640021
    | exact resolve eq640021 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640021
  have eq640123 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq640122
  have eq640151 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq640123 eq255
    | (have j0 := eq255 (σ x) X0
       grind)
    | (have r₁ := eq255 (σ x) x
       have r₂ := eq640123
       grind)
    | exact resolve eq255 eq640123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640123
  have eq640194 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq640151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640151
  have eq640221 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq640194 eq32
    | (have j1 := eq640194 (σ y)
       grind)
    | exact resolve eq32 eq640194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640194
  have eq640243 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq640221 eq33
    | exact resolve eq33 eq640221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640249 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq640221 eq602080
    | exact resolve eq602080 eq640221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602080 eq640221
  have eq640255 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq640249
       have r₂ := eq602613
       grind)
    | exact resolve eq640249 eq602613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602613 eq640249
  have eq640257 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq640243
       have r₂ := eq4822
       grind)
    | exact resolve eq640243 eq4822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4822 eq640243
  have eq640261 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq640255
       have r₂ := eq602106
       grind)
    | exact resolve eq640255 eq602106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602106 eq640255
  have eq640268 : (M.op x y) = (τ (k (σ x) (σ x))) := by
    first
    | exact superpose eq640257 eq36
    | exact resolve eq36 eq640257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq640367 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq640268
       have i₂ := eq121 sF4 sF4
       grind)
    | exact superpose eq121 eq640268
    | exact resolve eq640268 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640268
  have eq640467 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq640367 eq15
    | exact resolve eq15 eq640367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640544 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq640467
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq640467
    | exact resolve eq640467 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640467
  have eq640761 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq640261 eq121
    | exact resolve eq121 eq640261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq640261
  have eq640830 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq640367 eq640761
    | exact resolve eq640761 eq640367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640761
  have eq640831 : (M.op x y) = (τ (σ x)) := by grind
  clear eq640830
  have eq640854 : (M.op x y) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq640831 eq42
    | exact resolve eq42 eq640831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq641675 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq640831 eq640367
    | exact resolve eq640367 eq640831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640367
  have eq641676 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq640831 eq35
    | exact resolve eq35 eq640831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640831
  have eq641982 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq641676 eq640544
    | exact resolve eq640544 eq641676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640544
  have eq641983 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq641676 eq26
    | exact resolve eq26 eq641676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641676
  have eq643843 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq641675 eq255
    | (have j0 := eq255 (M.op x y) X0
       grind)
    | (have r₁ := eq255 (M.op x y) x
       have r₂ := eq641675
       grind)
    | exact resolve eq255 eq641675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641675
  have eq643883 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq643843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643843
  have eq644117 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq641982 eq255
    | (have j0 := eq255 (σ x) X0
       grind)
    | (have r₁ := eq255 (σ x) x
       have r₂ := eq641982
       grind)
    | exact resolve eq255 eq641982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq644160 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq644117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644117
  have eq644397 : (M.op x y) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq643883 eq640854
    | exact resolve eq640854 eq643883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640854 eq643883
  have eq644481 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq644397 eq15
    | exact resolve eq15 eq644397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644397
  have eq644544 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq644481
    | exact resolve eq644481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq644481
  have eq644545 : (k (σ x) (σ x)) = (k (σ (τ (σ y))) (k (σ x) (σ x))) := by
    first
    | exact superpose eq640257 eq644544
    | exact resolve eq644544 eq640257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640257 eq644544
  have eq644546 : (σ x) = (k (σ (τ (σ y))) (σ x)) := by
    first
    | exact superpose eq641982 eq644545
    | exact resolve eq644545 eq641982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641982 eq644545
  have eq644547 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq644546
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq644546
    | exact resolve eq644546 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq644546
  have eq645097 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq644160 eq32
    | (have j1 := eq644160 (σ y)
       grind)
    | exact resolve eq32 eq644160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq644160
  have eq645110 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq644547 eq645097
    | exact resolve eq645097 eq644547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644547 eq645097
  have eq645178 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq645110 eq33
    | exact resolve eq33 eq645110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq645110
  have eq645204 : False := by grind
  exact eq645204
