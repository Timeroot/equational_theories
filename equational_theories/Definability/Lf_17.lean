import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq66
    | (have j0 := eq66 X0
       grind)
    | exact resolve eq66 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq66
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq71
    | (have j0 := eq71 X0
       grind)
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq72 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq72 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq13
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq75
  have eq98 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq14
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq457 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq48
    | exact resolve eq48 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq457
    | (have j0 := eq457 X0 X1
       grind)
    | exact resolve eq457 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq98
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq98
       have r₂ := eq12 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq98
       have r₂ := eq12 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq98 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq684 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq683
  have eq3566 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq14
    | exact resolve eq14 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3567 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq10
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq684
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq684
       grind)
    | exact resolve eq10 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq3568 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq3567
  have eq3570 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3568
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3568
    | exact resolve eq3568 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq6063 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq487 x y
       have i₂ := eq3570
       grind)
    | exact superpose eq3570 eq487
    | (have j0 := eq487 x y
       grind)
    | exact resolve eq487 eq3570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq3570
  have eq6109 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6063
  have eq6133 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6109
       have r₂ := eq3566
       grind)
    | exact resolve eq6109 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566 eq6109
  have eq6252 : y ≠ y ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq6133
       grind)
    | exact superpose eq6133 eq10
    | (have r₁ := eq10 x y
       have r₂ := eq6133
       grind)
    | exact resolve eq10 eq6133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6253 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6252
  have eq6419 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100 x y
       have i₂ := eq6253
       grind)
    | exact superpose eq6253 eq100
    | (have j0 := eq100 x y
       grind)
    | exact resolve eq100 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq6253
  have eq6422 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6419
  have eq6423 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6422
  have eq6592 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq6423
       grind)
    | exact superpose eq6423 eq14
    | exact resolve eq14 eq6423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423
  have eq6817 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6592
       have i₂ := eq6133
       grind)
    | exact superpose eq6133 eq6592
    | exact resolve eq6592 eq6133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6133 eq6592
  have eq6818 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6817
  have eq6819 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6818
  have eq6841 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq6819
       grind)
    | exact superpose eq6819 eq8
    | exact resolve eq8 eq6819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6819
  have eq6902 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6841
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq6841
    | exact resolve eq6841 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6841
  have eq6903 : x = y := by grind
  clear eq6902
  have eq7032 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6903
       grind)
    | exact superpose eq6903 eq14
    | exact resolve eq14 eq6903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6903
  have eq7033 : False := by grind
  exact eq7033

/-- `x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq33 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq17
  have eq34 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq10 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq104 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq104
    | (have j0 := eq104 X0 X1
       grind)
    | exact resolve eq104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq222 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq108 x y
       grind)
    | exact superpose eq108 eq14
    | (have j1 := eq108 x y
       grind)
    | exact resolve eq14 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq232 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq222
    | (have j0 := eq222 X0 X1
       grind)
    | exact resolve eq222 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq222
  have eq238 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34
    | exact resolve eq34 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq261 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq238 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq238
    | (have j0 := eq238 X0
       grind)
    | exact resolve eq238 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq262 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq232
    | exact resolve eq232 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq411 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq226
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq226
    | (have j1 := eq262 (σ x) (σ y)
       grind)
    | (have r₁ := eq226
       have r₂ := eq262 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq226
       have r₂ := eq262 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq226 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq262
  have eq414 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq411
  have eq484 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq414
       grind)
    | exact superpose eq414 eq8
    | exact resolve eq8 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq523 : x = y ∨ x = y := by
    first
    | (have i₁ := eq484
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq484
    | exact resolve eq484 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq524 : x = y := by grind
  clear eq523
  have eq602 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq524
       grind)
    | exact superpose eq524 eq14
    | exact resolve eq14 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq659 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq602
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq602
    | (have j1 := eq31 x
       grind)
    | exact resolve eq602 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq8459 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq659
       have i₂ := eq261 x
       grind)
    | exact superpose eq261 eq659
    | (have j1 := eq261 (σ x)
       grind)
    | (have r₁ := eq659
       have r₂ := eq261 x
       grind)
    | exact resolve eq659 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq8460 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq8459
  have eq8650 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq602
       have i₂ := eq8460
       grind)
    | exact superpose eq8460 eq602
    | exact resolve eq602 eq8460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8651 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (σ x) (σ x)
       have i₂ := eq8460
       grind)
    | exact superpose eq8460 eq10
    | (have r₁ := eq10 (σ x) (σ x)
       have r₂ := eq8460
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq8460
       grind)
    | exact resolve eq10 eq8460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8652 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq8651
  have eq8653 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8652
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq8652
    | exact resolve eq8652 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8652
  have eq8942 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq261 x
       have i₂ := eq8653
       grind)
    | exact superpose eq8653 eq261
    | (have j0 := eq261 x
       grind)
    | exact resolve eq261 eq8653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq8653
  have eq9017 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq8942
  have eq9038 : x = (M.op x x) := by
    first
    | (have r₁ := eq9017
       have r₂ := eq8650
       grind)
    | exact resolve eq9017 eq8650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8650 eq9017
  have eq9140 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq9038
       grind)
    | exact superpose eq9038 eq10
    | (have r₁ := eq10 x x
       have r₂ := eq9038
       grind)
    | exact resolve eq10 eq9038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9141 : x = (k x x) := by grind
  clear eq9140
  have eq9350 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq9141
       grind)
    | exact superpose eq9141 eq70
    | (have j0 := eq70 x
       grind)
    | exact resolve eq70 eq9141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq9141
  have eq9360 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq9350
  have eq9775 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq602
       have i₂ := eq9360
       grind)
    | exact superpose eq9360 eq602
    | exact resolve eq602 eq9360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq9360
  have eq9779 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq9775
       have i₂ := eq9038
       grind)
    | exact superpose eq9038 eq9775
    | exact resolve eq9775 eq9038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9038 eq9775
  have eq9780 : False := by grind
  exact eq9780

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq62 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq62 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq193 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq198 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       have j1 := eq65 X1 X0
       grind)
    | (have r₁ := eq193 X1 X0
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq193 X0 X0
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq193 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq193
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq198 (σ X0) (σ X1)
       grind)
    | exact superpose eq198 eq13
    | exact resolve eq13 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq220 X0 X1
       have i₂ := eq198 X0 X1
       grind)
    | exact superpose eq198 eq220
    | exact resolve eq220 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq220
  have eq1213 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq227 x y
       grind)
    | exact superpose eq227 eq14
    | (have r₁ := eq14
       have r₂ := eq227 x y
       grind)
    | exact resolve eq14 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq1243 : False := by grind
  exact eq1243

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq61 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq59 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq59 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq60 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq60 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq60 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq70 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq61 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq78 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq68
    | (have j0 := eq68 X0 X1
       grind)
    | exact resolve eq68 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq68
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       have j1 := eq64 X1 X0
       grind)
    | (have r₁ := eq70 X0 X1
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq70 X1 X0
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq70 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq70
  have eq190 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq195 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq190 X0 X0
       have r₂ := eq78 X0 X0
       grind)
    | (have r₁ := eq190 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq190 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq190
  have eq216 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq195 (σ X1) (σ X0)
       grind)
    | exact superpose eq195 eq13
    | exact resolve eq13 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq195 X1 X0
       grind)
    | exact superpose eq195 eq216
    | exact resolve eq216 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq216
  have eq920 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq223 x y
       grind)
    | exact superpose eq223 eq14
    | (have r₁ := eq14
       have r₂ := eq223 x y
       grind)
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq952 : False := by grind
  exact eq952

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq83 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq56 X0 X1
       grind)
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X1)
       have r₂ := eq56 X1 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X0)
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq10 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq56 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq11
    | (have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq11 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq213 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq220 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       have j1 := eq83 X1 (σ X0)
       grind)
    | (have r₁ := eq213 X0 X0
       have r₂ := eq83 X0 (σ X0)
       grind)
    | exact resolve eq213 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq221 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       have j1 := eq83 X1 (σ X0)
       grind)
    | (have r₁ := eq189 X0 X0
       have r₂ := eq83 X0 (σ X0)
       grind)
    | exact resolve eq189 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq189
  have eq242 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq220 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq220
    | (have j0 := eq220 X0 X1
       grind)
    | exact resolve eq220 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq221
    | (have j0 := eq221 X0 X1
       grind)
    | exact resolve eq221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq221
  have eq257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq242
    | (have j0 := eq242 X0 X1
       grind)
    | exact resolve eq242 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq258 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq257 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq243
    | (have j0 := eq243 X0 X1
       grind)
    | exact resolve eq243 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq260 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq269 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq260 X0 X1
       have j1 := eq258 X0 X1
       grind)
    | (have r₁ := eq260 X0 X1
       have r₂ := eq258 X0 X1
       grind)
    | exact resolve eq260 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq260
  have eq272 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq269 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq269
    | exact resolve eq269 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq269 x y
       grind)
    | exact superpose eq269 eq14
    | exact resolve eq14 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq585 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X0)
       have i₂ := eq272 X0 (τ X1)
       grind)
    | exact superpose eq272 eq16
    | exact resolve eq16 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq272
  have eq616 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq585
    | exact resolve eq585 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq630 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq616
    | exact resolve eq616 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq781 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq288
       have i₂ := eq630 x y
       grind)
    | exact superpose eq630 eq288
    | exact resolve eq288 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq630
  have eq782 : False := by grind
  exact eq782

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq82 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq136 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq137 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq54 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq11 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq269 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq277 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       have j1 := eq82 X0 (σ X1)
       grind)
    | (have r₁ := eq269 X0 X1
       have r₂ := eq82 X0 (σ X1)
       grind)
    | exact resolve eq269 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq269
  have eq295 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq277 X0 X0
       have r₂ := eq10 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq277 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq305 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | exact resolve eq295 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq306 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq330 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq306 x y
       grind)
    | exact superpose eq306 eq14
    | exact resolve eq14 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq368 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq330
       have i₂ := eq137 x y
       grind)
    | exact superpose eq137 eq330
    | (have j1 := eq137 y x
       grind)
    | exact resolve eq330 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq377 : (M.op x y) = (M.op y x) := by grind
  clear eq368
  have eq440 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq377
       grind)
    | exact superpose eq377 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq377
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq377
       grind)
    | exact resolve eq11 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq442 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq440
  have eq444 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq10 y x
       grind)
    | (have r₁ := eq442
       have r₂ := eq10 y x
       grind)
    | exact resolve eq442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq515 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq330
       have i₂ := eq444
       grind)
    | exact superpose eq444 eq330
    | exact resolve eq330 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq444
  have eq516 : False := by grind
  exact eq516

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq64 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq64 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq64 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq215 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq222 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq215 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq215 X1 X0
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq215 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq215
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq222 (σ X0) (σ X1)
       grind)
    | exact superpose eq222 eq13
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq222 X0 X1
       grind)
    | exact superpose eq222 eq250
    | exact resolve eq250 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq250
  have eq1282 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq257 x y
       grind)
    | exact superpose eq257 eq14
    | (have r₁ := eq14
       have r₂ := eq257 x y
       grind)
    | exact resolve eq14 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq1314 : False := by grind
  exact eq1314

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
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
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq51 (σ X1) (σ X0)
       grind)
    | exact superpose eq51 eq13
    | (have j1 := eq51 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq51 (τ X1) X0
       grind)
    | exact superpose eq51 eq16
    | (have j1 := eq51 (τ X1) X0
       grind)
    | exact resolve eq16 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq51
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq74
    | exact resolve eq74 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq437 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq399
    | (have j0 := eq399 X0 X1
       grind)
    | exact resolve eq399 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq599 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq14
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq14 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq599
       have i₂ := eq437 y x
       grind)
    | exact superpose eq437 eq599
    | (have j1 := eq437 (σ y) (σ x)
       grind)
    | (have r₁ := eq599
       have r₂ := eq437 y x
       grind)
    | exact resolve eq599 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq2160 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2159
  have eq2164 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2160
       grind)
    | exact superpose eq2160 eq14
    | exact resolve eq14 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2167 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2160
       grind)
    | exact superpose eq2160 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2160
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2160
       grind)
    | exact resolve eq11 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2169 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2167
  have eq2171 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2169
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq2169
    | exact resolve eq2169 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2169
  have eq2174 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2171
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2171
    | exact resolve eq2171 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq40370 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81 y (σ x)
       have i₂ := eq2174
       grind)
    | exact superpose eq2174 eq81
    | (have j0 := eq81 y (σ x)
       grind)
    | (have r₁ := eq81 y (σ x)
       have r₂ := eq2174
       grind)
    | exact resolve eq81 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2174
  have eq40399 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq40370
  have eq40425 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40399
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq40399
    | exact resolve eq40399 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40399
  have eq70207 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2160
       have i₂ := eq40425
       grind)
    | exact superpose eq40425 eq2160
    | exact resolve eq2160 eq40425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160 eq40425
  have eq70216 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq70207
  have eq71252 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq437 y x
       have i₂ := eq70216
       grind)
    | exact superpose eq70216 eq437
    | (have j0 := eq437 y x
       grind)
    | exact resolve eq437 eq70216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq70216
  have eq71332 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq71252
  have eq71357 : x = (M.op x y) := by
    first
    | (have r₁ := eq71332
       have r₂ := eq2164
       grind)
    | exact resolve eq71332 eq2164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164 eq71332
  have eq72079 : x ≠ x ∨ (M.op y y) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq71357
       grind)
    | exact superpose eq71357 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq71357
       grind)
    | exact resolve eq11 eq71357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72082 : x = (k x y) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq72079
  have eq73993 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq610 x y
       have i₂ := eq72082
       grind)
    | exact superpose eq72082 eq610
    | (have j0 := eq610 x y
       grind)
    | exact resolve eq610 eq72082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72082
  have eq74062 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq73993
  have eq75679 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq74062
       grind)
    | exact superpose eq74062 eq14
    | exact resolve eq14 eq74062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74062
  have eq75689 : (σ x) ≠ (σ x) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq75679
       have i₂ := eq71357
       grind)
    | exact superpose eq71357 eq75679
    | exact resolve eq75679 eq71357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75679
  have eq75690 : (M.op y y) = (M.op y x) := by grind
  clear eq75689
  have eq76477 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq75690
       grind)
    | exact superpose eq75690 eq10
    | (have j0 := eq10 X0 y
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq75690
       grind)
    | exact resolve eq10 eq75690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75690
  have eq77365 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq76477 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76477
  have eq77367 : x = (k x y) := by
    first
    | (have i₁ := eq77365
       have i₂ := eq71357
       grind)
    | exact superpose eq71357 eq77365
    | exact resolve eq77365 eq71357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77365
  have eq78174 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq610 x y
       have i₂ := eq77367
       grind)
    | exact superpose eq77367 eq610
    | (have j0 := eq610 x y
       grind)
    | exact resolve eq610 eq77367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq77367
  have eq78244 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq78174
  have eq79906 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq78244
       grind)
    | exact superpose eq78244 eq14
    | exact resolve eq14 eq78244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78244
  have eq79916 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq79906
       have i₂ := eq71357
       grind)
    | exact superpose eq71357 eq79906
    | exact resolve eq79906 eq71357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71357 eq79906
  have eq79917 : False := by grind
  exact eq79917
