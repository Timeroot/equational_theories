import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxy_pyy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq10 X1 X0
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq9
    | (have j0 := eq9 X0 X0
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq9 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq9 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq9 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq65 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq69 (σ X0) (σ X1)
       grind)
    | exact superpose eq69 eq11
    | exact resolve eq11 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq85
    | exact resolve eq85 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq85
  have eq977 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq12
    | (have r₁ := eq12
       have r₂ := eq90 x y
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq990 : False := by grind
  exact eq990

/-- `x □ y = if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxy_x_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq10 (σ X0) (σ X1)
       grind)
    | exact superpose eq10 eq11
    | (have j1 := eq10 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq16 x y
       grind)
    | exact superpose eq16 eq12
    | (have j1 := eq16 x y
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq252 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq46
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq253 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq252
  have eq255 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq12
    | exact resolve eq12 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq9
    | (have j0 := eq9 (σ x) (σ y)
       grind)
    | (have r₁ := eq9 (σ x) (σ y)
       have r₂ := eq253
       grind)
    | (have r₁ := eq9 x y
       have r₂ := eq253
       grind)
    | exact resolve eq9 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq257 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq256
  have eq258 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq257
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq257
    | exact resolve eq257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq322 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq258
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq258
    | (have j1 := eq10 x y
       grind)
    | exact resolve eq258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq346 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq322
  have eq360 : x = (M.op x y) := by
    first
    | (have r₁ := eq346
       have r₂ := eq255
       grind)
    | exact resolve eq346 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq346
  have eq391 : x ≠ x ∨ x = (k x y) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq9
    | (have j0 := eq9 x y
       grind)
    | (have r₁ := eq9 x y
       have r₂ := eq360
       grind)
    | exact resolve eq9 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : x = (k x y) := by grind
  clear eq391
  have eq431 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq392
       grind)
    | exact superpose eq392 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq392
  have eq434 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq431
  have eq449 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq12
       have i₂ := eq434
       grind)
    | exact superpose eq434 eq12
    | exact resolve eq12 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq453 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq449
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq449
    | exact resolve eq449 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq449
  have eq454 : False := by grind
  exact eq454

/-- `x □ y = if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxy_y_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq10 (σ X0) (σ X1)
       grind)
    | exact superpose eq10 eq11
    | (have j1 := eq10 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq16 x y
       grind)
    | exact superpose eq16 eq12
    | (have j1 := eq16 x y
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq252 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq46
    | (have j1 := eq10 (σ x) (σ y)
       grind)
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq253 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq252
  have eq255 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq12
    | exact resolve eq12 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq9
    | (have j0 := eq9 (σ x) (σ y)
       grind)
    | (have r₁ := eq9 (σ x) (σ y)
       have r₂ := eq253
       grind)
    | (have r₁ := eq9 x y
       have r₂ := eq253
       grind)
    | exact resolve eq9 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq257 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq256
  have eq258 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq257
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq257
    | exact resolve eq257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq322 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq258
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq258
    | (have j1 := eq10 x y
       grind)
    | exact resolve eq258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq346 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq322
  have eq360 : y = (M.op x y) := by
    first
    | (have r₁ := eq346
       have r₂ := eq255
       grind)
    | exact resolve eq346 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq346
  have eq391 : y ≠ y ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq9
    | (have j0 := eq9 x y
       grind)
    | (have r₁ := eq9 x y
       have r₂ := eq360
       grind)
    | exact resolve eq9 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : y = (k x y) := by grind
  clear eq391
  have eq431 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq392
       grind)
    | exact superpose eq392 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq392
  have eq434 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq431
  have eq449 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq434
       grind)
    | exact superpose eq434 eq12
    | exact resolve eq12 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq453 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq449
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq449
    | exact resolve eq449 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq449
  have eq454 : False := by grind
  exact eq454

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pyx_pyy_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq10 X1 X0
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq9
    | (have j0 := eq9 X0 X0
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq9 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq9 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq9 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq65 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq85 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq69 (σ X1) (σ X0)
       grind)
    | exact superpose eq69 eq11
    | exact resolve eq11 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq85
    | exact resolve eq85 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq85
  have eq972 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq12
    | (have r₁ := eq12
       have r₂ := eq90 x y
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq985 : False := by grind
  exact eq985

/-- `x □ y = if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pyx_x_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact superpose eq10 eq11
    | (have j1 := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq16 x y
       grind)
    | exact superpose eq16 eq12
    | (have j1 := eq16 x y
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq252 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq46
    | (have j1 := eq10 (σ y) (σ x)
       grind)
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq253 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq252
  have eq255 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq12
    | exact resolve eq12 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq9
    | (have j0 := eq9 (σ y) (σ x)
       grind)
    | (have r₁ := eq9 (σ y) (σ x)
       have r₂ := eq253
       grind)
    | (have r₁ := eq9 y x
       have r₂ := eq253
       grind)
    | exact resolve eq9 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq257 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq256
  have eq258 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq257
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq257
    | exact resolve eq257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq322 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq258
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq258
    | (have j1 := eq10 y x
       grind)
    | exact resolve eq258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq346 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq322
  have eq360 : y = (M.op x y) := by
    first
    | (have r₁ := eq346
       have r₂ := eq255
       grind)
    | exact resolve eq346 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq346
  have eq391 : y ≠ y ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq9
    | (have j0 := eq9 y x
       grind)
    | (have r₁ := eq9 y x
       have r₂ := eq360
       grind)
    | exact resolve eq9 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : y = (k y x) := by grind
  clear eq391
  have eq431 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq392
       grind)
    | exact superpose eq392 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq392
  have eq434 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq431
  have eq449 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq434
       grind)
    | exact superpose eq434 eq12
    | exact resolve eq12 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq453 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq449
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq449
    | exact resolve eq449 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq449
  have eq454 : False := by grind
  exact eq454

/-- `x □ y = if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pyx_y_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact superpose eq10 eq11
    | (have j1 := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq16 x y
       grind)
    | exact superpose eq16 eq12
    | (have j1 := eq16 x y
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq252 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq46
    | (have j1 := eq10 (σ y) (σ x)
       grind)
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq253 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq252
  have eq255 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq12
    | exact resolve eq12 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq253
       grind)
    | exact superpose eq253 eq9
    | (have j0 := eq9 (σ y) (σ x)
       grind)
    | (have r₁ := eq9 (σ y) (σ x)
       have r₂ := eq253
       grind)
    | (have r₁ := eq9 y x
       have r₂ := eq253
       grind)
    | exact resolve eq9 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq257 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq256
  have eq258 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq257
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq257
    | exact resolve eq257 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq322 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq258
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq258
    | (have j1 := eq10 y x
       grind)
    | exact resolve eq258 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq346 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq322
  have eq360 : x = (M.op x y) := by
    first
    | (have r₁ := eq346
       have r₂ := eq255
       grind)
    | exact resolve eq346 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq346
  have eq391 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq9
    | (have j0 := eq9 y x
       grind)
    | (have r₁ := eq9 y x
       have r₂ := eq360
       grind)
    | exact resolve eq9 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : x = (k y x) := by grind
  clear eq391
  have eq431 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq392
       grind)
    | exact superpose eq392 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq392
  have eq434 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq431
  have eq449 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq12
       have i₂ := eq434
       grind)
    | exact superpose eq434 eq12
    | exact resolve eq12 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq453 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq449
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq449
    | exact resolve eq449 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq449
  have eq454 : False := by grind
  exact eq454
