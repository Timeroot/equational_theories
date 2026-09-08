import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxx_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq9
    | (have j0 := eq9 X0 X0
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq9 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq9 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | exact resolve eq9 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq65 X1 X1
       have r₂ := eq10 X1 X1
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
  have eq974 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq987 : False := by grind
  exact eq987

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq9
    | (have j0 := eq9 X0 X0
       have j1 := eq10 X0 X1
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
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
  have eq975 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq988 : False := by grind
  exact eq988

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxx_pyy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq19 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq9 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq19 (σ X0)
       grind)
    | exact superpose eq19 eq11
    | exact resolve eq11 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq10 X2 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq9
    | (have j0 := eq9 X0 X1
       have j1 := eq10 X2 X0
       grind)
    | (have r₁ := eq9 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq9 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq9 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq10 X1 X0
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq9
    | (have j0 := eq9 X0 X2
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq9 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq9 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq9 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact superpose eq10 eq11
    | (have j1 := eq10 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq77 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7 (M.op X1 X1)
       have i₂ := eq40 X0 X1
       grind)
    | (have i₁ := eq7 (M.op X0 X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq7
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq7 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq7 (M.op X0 X0)
       grind)
    | exact superpose eq7 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq154 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | (have j0 := eq9 (σ X0) X1
       grind)
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq415 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq498 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq352 (σ X0) (σ X1)
       grind)
    | exact superpose eq352 eq11
    | (have j1 := eq352 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq498
    | (have j0 := eq498 X0 X1
       grind)
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq539 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq415 (σ X0) (σ X1)
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq415
    | exact resolve eq415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq1130 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq12
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3277 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1130
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1130
    | (have j1 := eq10 x y
       grind)
    | exact resolve eq1130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1130
       have i₂ := eq352 x y
       grind)
    | exact superpose eq352 eq1130
    | (have j1 := eq352 x y
       grind)
    | exact resolve eq1130 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq1130
  have eq3287 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq3285
  have eq3294 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq3277
  have eq3295 : (M.op x x) = (M.op y y) := by grind
  clear eq3294
  have eq3296 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq9 x y
       grind)
    | (have r₁ := eq3287
       have r₂ := eq9 x y
       grind)
    | (have r₁ := eq3287
       have r₂ := eq9 y x
       grind)
    | exact resolve eq3287 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287
  have eq3589 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq3295
       grind)
    | exact superpose eq3295 eq9
    | (have j0 := eq9 X0 x
       grind)
    | (have r₁ := eq9 x y
       have r₂ := eq3295
       grind)
    | (have r₁ := eq9 y x
       have r₂ := eq3295
       grind)
    | exact resolve eq9 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4433 : (k y x) = (M.op y x) := by
    first
    | (have j0 := eq3589 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq14063 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq154 y X0
       have i₂ := eq3295
       grind)
    | exact superpose eq3295 eq154
    | (have j0 := eq154 x X0
       grind)
    | exact resolve eq154 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq3295
  have eq36180 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14063 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq14063
    | (have j0 := eq14063 (σ X0)
       grind)
    | (have r₁ := eq14063 (σ x)
       have r₂ := eq24 x
       grind)
    | exact resolve eq14063 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14063
  have eq36264 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq36180 X0
       have i₂ := eq11 y X0
       grind)
    | exact superpose eq11 eq36180
    | (have j0 := eq36180 X0
       grind)
    | exact resolve eq36180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36180
  have eq71102 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq509 x y
       grind)
    | exact superpose eq509 eq12
    | (have j1 := eq509 x y
       grind)
    | exact resolve eq12 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq71118 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq71102
       have i₂ := eq4433
       grind)
    | exact superpose eq4433 eq71102
    | exact resolve eq71102 eq4433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71102
  have eq71136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq71118
       have i₂ := eq3296
       grind)
    | exact superpose eq3296 eq71118
    | exact resolve eq71118 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71118
  have eq71141 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have r₁ := eq71136
       have r₂ := eq12
       grind)
    | exact resolve eq71136 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71136
  have eq80444 : (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have j0 := eq36264 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36264
  have eq80456 : (σ (M.op y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq80444
       have i₂ := eq4433
       grind)
    | exact superpose eq4433 eq80444
    | exact resolve eq80444 eq4433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4433 eq80444
  have eq80514 : (σ (M.op y x)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq539 x y
       have i₂ := eq80456
       grind)
    | exact superpose eq80456 eq539
    | (have j0 := eq539 x y
       grind)
    | exact resolve eq539 eq80456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq80456
  have eq80588 : (σ (M.op x y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq80514
       have i₂ := eq3296
       grind)
    | exact superpose eq3296 eq80514
    | exact resolve eq80514 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80514
  have eq80618 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq80588
       have r₂ := eq71141
       grind)
    | exact resolve eq80588 eq71141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71141 eq80588
  have eq80639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq80618
       have i₂ := eq3296
       grind)
    | exact superpose eq3296 eq80618
    | exact resolve eq80618 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296 eq80618
  have eq80657 : False := by grind
  exact eq80657

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxx_pyy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq19 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq9 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq19 (σ X0)
       grind)
    | exact superpose eq19 eq11
    | exact resolve eq11 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21 X0
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq77 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7 (M.op X1 X1)
       have i₂ := eq40 X0 X1
       grind)
    | (have i₁ := eq7 (M.op X0 X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq7
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq7 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq7 (M.op X0 X0)
       grind)
    | exact superpose eq7 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq154 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | (have j0 := eq9 (σ X0) X1
       grind)
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq12
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq12
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3272 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1130
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1130
    | (have j1 := eq10 x y
       grind)
    | exact resolve eq1130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq3284 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq3272
  have eq3285 : (M.op x x) = (M.op y y) := by grind
  clear eq3284
  have eq3578 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq3285
       grind)
    | exact superpose eq3285 eq9
    | (have j0 := eq9 X0 x
       grind)
    | (have r₁ := eq9 x y
       have r₂ := eq3285
       grind)
    | (have r₁ := eq9 y x
       have r₂ := eq3285
       grind)
    | exact resolve eq9 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3947 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq3578 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578
  have eq13825 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq154 y X0
       have i₂ := eq3285
       grind)
    | exact superpose eq3285 eq154
    | (have j0 := eq154 x X0
       grind)
    | exact resolve eq154 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq3285
  have eq34527 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13825 (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq13825
    | (have j0 := eq13825 (σ X0)
       grind)
    | (have r₁ := eq13825 (σ x)
       have r₂ := eq24 x
       grind)
    | exact resolve eq13825 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13825
  have eq34611 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34527 X0
       have i₂ := eq11 y X0
       grind)
    | exact superpose eq11 eq34527
    | (have j0 := eq34527 X0
       grind)
    | exact resolve eq34527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34527
  have eq85498 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq34611 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34611
  have eq85509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85498
       have i₂ := eq3947
       grind)
    | exact superpose eq3947 eq85498
    | exact resolve eq85498 eq3947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947 eq85498
  have eq85517 : False := by grind
  exact eq85517

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxy_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq28 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq28 X0 X1
       grind)
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9
    | (have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq9 (σ X1) (σ X0)
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq9 (σ X0) (σ X1)
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq11 X1 X0
       grind)
    | exact superpose eq11 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq127 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq12
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq127
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq127
    | (have j1 := eq10 x y
       grind)
    | exact resolve eq127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (M.op x y) = (M.op y x) := by grind
  clear eq162
  have eq192 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq163
       grind)
    | exact superpose eq163 eq9
    | (have r₁ := eq9 x y
       have r₂ := eq163
       grind)
    | (have r₁ := eq9 y x
       have r₂ := eq163
       grind)
    | exact resolve eq9 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq193 : (M.op x y) = (k y x) := by grind
  clear eq192
  have eq227 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq193
       grind)
    | exact superpose eq193 eq127
    | exact resolve eq127 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq193
  have eq228 : False := by grind
  exact eq228

/-- `x □ y = if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut_pxy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht he hd nh hi1 hi2
  have eq28 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq28 X0 X1
       grind)
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq9
    | (have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq9 (σ X0) (σ X1)
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq9 (σ X1) (σ X0)
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq9 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq54 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq126 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq12
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq12
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq126
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq126
    | (have j1 := eq10 x y
       grind)
    | exact resolve eq126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (M.op x y) = (M.op y x) := by grind
  clear eq161
  have eq190 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq162
       grind)
    | exact superpose eq162 eq9
    | (have r₁ := eq9 x y
       have r₂ := eq162
       grind)
    | (have r₁ := eq9 y x
       have r₂ := eq162
       grind)
    | exact resolve eq9 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq193 : (M.op x y) = (k x y) := by grind
  clear eq190
  have eq266 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq193
       grind)
    | exact superpose eq193 eq126
    | exact resolve eq126 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq193
  have eq267 : False := by grind
  exact eq267
