import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_x_y_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq10 (σ x) (σ y)
       grind)
    | exact superpose eq10 eq12
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq16
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq38 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq17
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq39 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq38
  have eq44 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7 y
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq7
    | exact resolve eq7 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : x = y ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq7 x
       grind)
    | exact superpose eq7 eq44
    | exact resolve eq44 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : x = y := by grind
  clear eq45
  have eq64 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq12
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq64
  have eq66 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq65
  have eq67 : False := by grind
  exact eq67

/-- `x □ y = if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_x_y_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq10 (σ y) (σ x)
       grind)
    | exact superpose eq10 eq12
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq16
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq38 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq17
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq39 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq38
  have eq44 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7 y
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq7
    | exact resolve eq7 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : x = y ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq7 x
       grind)
    | exact superpose eq7 eq44
    | exact resolve eq44 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : x = y := by grind
  clear eq45
  have eq64 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq12
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq64
  have eq66 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq65
  have eq67 : False := by grind
  exact eq67

/-- `x □ y = if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_x_y_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq10 (σ y) (σ x)
       grind)
    | exact superpose eq10 eq12
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq16
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq38 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq17
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq39 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq38
  have eq44 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7 y
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq7
    | exact resolve eq7 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : x = y ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq7 x
       grind)
    | exact superpose eq7 eq44
    | exact resolve eq44 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : x = y := by grind
  clear eq45
  have eq64 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq12
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq64
  have eq66 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq65
  have eq67 : False := by grind
  exact eq67

/-- `x □ y = if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_x_y_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq10 (σ x) (σ y)
       grind)
    | exact superpose eq10 eq12
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq16
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq38 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq17
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq39 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq38
  have eq44 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7 y
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq7
    | exact resolve eq7 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : x = y ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq7 x
       grind)
    | exact superpose eq7 eq44
    | exact resolve eq44 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : x = y := by grind
  clear eq45
  have eq64 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq12
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq64
  have eq66 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq65
  have eq67 : False := by grind
  exact eq67

/-- `x □ y = if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_x_y_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq10 (σ x) (σ y)
       grind)
    | exact superpose eq10 eq12
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq16
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq38 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq17
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq39 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq38
  have eq44 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7 y
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq7
    | exact resolve eq7 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : x = y ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq7 x
       grind)
    | exact superpose eq7 eq44
    | exact resolve eq44 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : x = y := by grind
  clear eq45
  have eq64 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq12
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq64
  have eq66 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq65
  have eq67 : False := by grind
  exact eq67

/-- `x □ y = if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_x_y_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq10 (σ y) (σ x)
       grind)
    | exact superpose eq10 eq12
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12
       have r₂ := eq10 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq16
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq38 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq17
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq17
       have r₂ := eq10 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq39 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq38
  have eq44 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7 y
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq7
    | exact resolve eq7 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : x = y ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq7 x
       grind)
    | exact superpose eq7 eq44
    | exact resolve eq44 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : x = y := by grind
  clear eq45
  have eq64 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq12
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq64
  have eq66 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq65
  have eq67 : False := by grind
  exact eq67
