import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pyx_x_pyx_x_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41 (σ y) (σ x)
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq41 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq41 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq41 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq41 X0 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq58 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq58 (M.op X0 X1) (M.op X0 X0)
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq58 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq54
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq77 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq24 (τ X0)
       grind)
    | exact superpose eq24 eq19
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq80
    | exact resolve eq80 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq80
  have eq91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq88 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq60
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq60
    | (have j1 := eq41 (M.op (σ x) (σ y)) (σ (k y x))
       grind)
    | (have r₁ := eq60
       have r₂ := eq41 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq60
       have r₂ := eq41 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq60 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq99
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq59 (τ X1) X0
       grind)
    | exact superpose eq59 eq18
    | (have j1 := eq59 (τ X1) X0
       grind)
    | exact resolve eq18 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq59 X1 (τ X0)
       grind)
    | exact superpose eq59 eq19
    | (have j1 := eq59 X1 (τ X0)
       grind)
    | exact resolve eq19 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq59
  have eq258 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq280 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq258
    | (have j0 := eq258 X0 X1
       grind)
    | exact resolve eq258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq290 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq105 X1 X0
       grind)
    | exact superpose eq105 eq18
    | (have j1 := eq105 X1 X0
       grind)
    | exact resolve eq18 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq105
  have eq299 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (k X0 (σ X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq347 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq348 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq347
       have r₂ := eq91 x
       grind)
    | exact resolve eq347 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq404 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 y x
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 y x
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1371 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq299 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq299
    | (have j0 := eq299 (σ X0) X1
       grind)
    | exact resolve eq299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq1410 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1371 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1371
    | (have j0 := eq1371 X0 X1
       grind)
    | exact resolve eq1371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1414 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1410 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1410
    | (have j0 := eq1410 X0 X1
       grind)
    | exact resolve eq1410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1774 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq404
       have i₂ := eq348
       grind)
    | exact superpose eq348 eq404
    | exact resolve eq404 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq404
  have eq1775 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq1774
  have eq1776 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq1775
  have eq1777 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1776
       have r₂ := eq60
       grind)
    | exact resolve eq1776 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1776
  have eq1779 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1777
       grind)
    | exact superpose eq1777 eq16
    | exact resolve eq16 eq1777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1859 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq1779
       have i₂ := eq1414 y x
       grind)
    | exact superpose eq1414 eq1779
    | (have j1 := eq1414 y x
       grind)
    | (have r₁ := eq1779
       have r₂ := eq1414 y x
       grind)
    | (have r₁ := eq1779
       have r₂ := eq1414 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1779
       have r₂ := eq1414 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1779 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1861 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq1779
       have i₂ := eq280 x y
       grind)
    | exact superpose eq280 eq1779
    | (have j1 := eq280 x y
       grind)
    | (have r₁ := eq1779
       have r₂ := eq280 x y
       grind)
    | (have r₁ := eq1779
       have r₂ := eq280 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1779
       have r₂ := eq280 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1779 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq1862 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq1861
  have eq1863 : x = y ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq1859
  have eq1940 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1862
       grind)
    | exact superpose eq1862 eq16
    | exact resolve eq16 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq1941 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1940
       have r₂ := eq91 x
       grind)
    | exact resolve eq1940 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq2015 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1779
       have i₂ := eq1941
       grind)
    | exact superpose eq1941 eq1779
    | exact resolve eq1779 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779 eq1941
  have eq2018 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq2015
  have eq2088 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2018
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq2018
    | (have j1 := eq41 (σ x) (σ y)
       grind)
    | (have r₁ := eq2018
       have r₂ := eq41 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq2018
       have r₂ := eq41 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq2018 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2089 : (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq2088
  have eq2269 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1863
       grind)
    | exact superpose eq1863 eq16
    | exact resolve eq16 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq2270 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq2269
       have r₂ := eq91 x
       grind)
    | exact resolve eq2269 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2272 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq2270
       grind)
    | exact superpose eq2270 eq9
    | exact resolve eq9 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2314 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq2272
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2272
    | exact resolve eq2272 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2316 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2314
       grind)
    | exact superpose eq2314 eq16
    | exact resolve eq16 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314
  have eq2317 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq2316
       have r₂ := eq91 x
       grind)
    | exact resolve eq2316 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316
  have eq2402 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq2317
       grind)
    | exact superpose eq2317 eq9
    | exact resolve eq9 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq2445 : y = (k y x) := by
    first
    | (have i₁ := eq2402
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2402
    | exact resolve eq2402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq3091 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2089
       have i₂ := eq2445
       grind)
    | exact superpose eq2445 eq2089
    | exact resolve eq2089 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089 eq2445
  have eq3092 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2018
       have i₂ := eq3091
       grind)
    | exact superpose eq3091 eq2018
    | exact resolve eq2018 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018 eq3091
  have eq3103 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3092
  have eq3104 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3103
  have eq3105 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3104
       grind)
    | exact superpose eq3104 eq16
    | exact resolve eq16 eq3104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104
  have eq3110 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3105
       have r₂ := eq91 x
       grind)
    | exact resolve eq3105 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq3112 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq3110
       grind)
    | exact superpose eq3110 eq9
    | exact resolve eq9 eq3110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq3162 : x = y := by
    first
    | (have i₁ := eq3112
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3112
    | exact resolve eq3112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq3316 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3162
       grind)
    | exact superpose eq3162 eq16
    | exact resolve eq16 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq3321 : False := by grind
  exact eq3321

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then Y else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pyx_x_pyx_y_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41 (σ y) (σ x)
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq41 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq41 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq41 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq41 X0 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq58 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq58 (M.op X0 X1) (M.op X0 X0)
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq58 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq54
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq77 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq24 (τ X0)
       grind)
    | exact superpose eq24 eq19
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq80
    | exact resolve eq80 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq80
  have eq91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq88 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq60
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq60
    | (have j1 := eq41 (M.op (σ x) (σ y)) (σ (k y x))
       grind)
    | (have r₁ := eq60
       have r₂ := eq41 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq60
       have r₂ := eq41 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq60 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq99
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq59 (τ X1) X0
       grind)
    | exact superpose eq59 eq18
    | (have j1 := eq59 (τ X1) X0
       grind)
    | exact resolve eq18 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq59 X1 (τ X0)
       grind)
    | exact superpose eq59 eq19
    | (have j1 := eq59 X1 (τ X0)
       grind)
    | exact resolve eq19 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq59
  have eq258 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq280 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq258 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq258
    | (have j0 := eq258 X0 X1
       grind)
    | exact resolve eq258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq290 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq105 X1 X0
       grind)
    | exact superpose eq105 eq18
    | (have j1 := eq105 X1 X0
       grind)
    | exact resolve eq18 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq105
  have eq299 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (k X0 (σ X1)) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq347 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq348 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq347
       have r₂ := eq91 x
       grind)
    | exact resolve eq347 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq404 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 y x
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 y x
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1371 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq299 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq299
    | (have j0 := eq299 (σ X0) X1
       grind)
    | exact resolve eq299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq1410 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1371 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1371
    | (have j0 := eq1371 X0 X1
       grind)
    | exact resolve eq1371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1414 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1410 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1410
    | (have j0 := eq1410 X0 X1
       grind)
    | exact resolve eq1410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1774 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq404
       have i₂ := eq348
       grind)
    | exact superpose eq348 eq404
    | exact resolve eq404 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq404
  have eq1775 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq1774
  have eq1776 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq1775
  have eq1777 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1776
       have r₂ := eq60
       grind)
    | exact resolve eq1776 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1776
  have eq1779 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1777
       grind)
    | exact superpose eq1777 eq16
    | exact resolve eq16 eq1777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1859 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq1779
       have i₂ := eq1414 y x
       grind)
    | exact superpose eq1414 eq1779
    | (have j1 := eq1414 y x
       grind)
    | (have r₁ := eq1779
       have r₂ := eq1414 y x
       grind)
    | (have r₁ := eq1779
       have r₂ := eq1414 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1779
       have r₂ := eq1414 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1779 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1861 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq1779
       have i₂ := eq280 x y
       grind)
    | exact superpose eq280 eq1779
    | (have j1 := eq280 x y
       grind)
    | (have r₁ := eq1779
       have r₂ := eq280 x y
       grind)
    | (have r₁ := eq1779
       have r₂ := eq280 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1779
       have r₂ := eq280 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1779 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq1862 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq1861
  have eq1863 : x = y ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq1859
  have eq1940 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1862
       grind)
    | exact superpose eq1862 eq16
    | exact resolve eq16 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq1941 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1940
       have r₂ := eq91 x
       grind)
    | exact resolve eq1940 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq2015 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1779
       have i₂ := eq1941
       grind)
    | exact superpose eq1941 eq1779
    | exact resolve eq1779 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779 eq1941
  have eq2018 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq2015
  have eq2088 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2018
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq2018
    | (have j1 := eq41 (σ x) (σ y)
       grind)
    | (have r₁ := eq2018
       have r₂ := eq41 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq2018
       have r₂ := eq41 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq2018 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2089 : (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq2088
  have eq2269 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1863
       grind)
    | exact superpose eq1863 eq16
    | exact resolve eq16 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq2270 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq2269
       have r₂ := eq91 x
       grind)
    | exact resolve eq2269 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2272 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq2270
       grind)
    | exact superpose eq2270 eq9
    | exact resolve eq9 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2314 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq2272
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2272
    | exact resolve eq2272 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2316 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2314
       grind)
    | exact superpose eq2314 eq16
    | exact resolve eq16 eq2314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314
  have eq2317 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq2316
       have r₂ := eq91 x
       grind)
    | exact resolve eq2316 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316
  have eq2402 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq2317
       grind)
    | exact superpose eq2317 eq9
    | exact resolve eq9 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq2445 : y = (k y x) := by
    first
    | (have i₁ := eq2402
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2402
    | exact resolve eq2402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq3091 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2089
       have i₂ := eq2445
       grind)
    | exact superpose eq2445 eq2089
    | exact resolve eq2089 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089 eq2445
  have eq3092 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2018
       have i₂ := eq3091
       grind)
    | exact superpose eq3091 eq2018
    | exact resolve eq2018 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018 eq3091
  have eq3103 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3092
  have eq3104 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3103
  have eq3105 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3104
       grind)
    | exact superpose eq3104 eq16
    | exact resolve eq16 eq3104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104
  have eq3110 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3105
       have r₂ := eq91 x
       grind)
    | exact resolve eq3105 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq3112 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq3110
       grind)
    | exact superpose eq3110 eq9
    | exact resolve eq9 eq3110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq3162 : x = y := by
    first
    | (have i₁ := eq3112
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3112
    | exact resolve eq3112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq3316 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3162
       grind)
    | exact superpose eq3162 eq16
    | exact resolve eq16 eq3162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq3321 : False := by grind
  exact eq3321

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else if m(Y,X) = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pyx_y_pyx_x_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41 (σ y) (σ x)
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq41 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq41 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq41 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq41 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq58 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq58 (M.op X0 X1) (M.op X0 X0)
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq58 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq54
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq77 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq24 (τ X0)
       grind)
    | exact superpose eq24 eq19
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq80
    | exact resolve eq80 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq80
  have eq91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq88 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq60
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq60
    | (have j1 := eq41 (M.op (σ x) (σ y)) (σ (k y x))
       grind)
    | (have r₁ := eq60
       have r₂ := eq41 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq60
       have r₂ := eq41 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq60 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq99
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq59 X0 (τ X1)
       grind)
    | exact superpose eq59 eq18
    | (have j1 := eq59 X0 (τ X1)
       grind)
    | exact resolve eq18 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq108 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq59 (τ X0) X1
       grind)
    | exact superpose eq59 eq19
    | (have j1 := eq59 (τ X0) X1
       grind)
    | exact resolve eq19 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq257 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq105
    | exact resolve eq105 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq279 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq257 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq257
    | (have j0 := eq257 X0 X1
       grind)
    | exact resolve eq257 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq289 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq19
    | (have j1 := eq108 X0 X1
       grind)
    | exact resolve eq19 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq108
  have eq298 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq289
    | (have j0 := eq289 X0 X1
       grind)
    | exact resolve eq289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq345 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq346 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq345
       have r₂ := eq91 x
       grind)
    | exact resolve eq345 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq403 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 y x
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 y x
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1292 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq298 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq298
    | (have j0 := eq298 (σ X0) X1
       grind)
    | exact resolve eq298 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1330 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1292 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1292
    | (have j0 := eq1292 X0 X1
       grind)
    | exact resolve eq1292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1334 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1330 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1330
    | (have j0 := eq1330 X0 X1
       grind)
    | exact resolve eq1330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq403
       have i₂ := eq346
       grind)
    | exact superpose eq346 eq403
    | exact resolve eq403 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq403
  have eq1711 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq1710
  have eq1712 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq1711
  have eq1713 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1712
       have r₂ := eq60
       grind)
    | exact resolve eq1712 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1712
  have eq1715 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1713
       grind)
    | exact superpose eq1713 eq16
    | exact resolve eq16 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq1715
       have i₂ := eq1334 x y
       grind)
    | exact superpose eq1334 eq1715
    | (have j1 := eq1334 x y
       grind)
    | (have r₁ := eq1715
       have r₂ := eq1334 x y
       grind)
    | (have r₁ := eq1715
       have r₂ := eq1334 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1715
       have r₂ := eq1334 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1715 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1799 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq1715
       have i₂ := eq279 y x
       grind)
    | exact superpose eq279 eq1715
    | (have j1 := eq279 y x
       grind)
    | (have r₁ := eq1715
       have r₂ := eq279 y x
       grind)
    | (have r₁ := eq1715
       have r₂ := eq279 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1715
       have r₂ := eq279 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1715 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq1800 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq1799
  have eq1801 : x = y ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq1797
  have eq1878 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1800
       grind)
    | exact superpose eq1800 eq16
    | exact resolve eq16 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1879 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1878
       have r₂ := eq91 x
       grind)
    | exact resolve eq1878 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq1955 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1715
       have i₂ := eq1879
       grind)
    | exact superpose eq1879 eq1715
    | exact resolve eq1715 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715 eq1879
  have eq1958 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq1955
  have eq2039 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1958
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq1958
    | (have j1 := eq41 (σ x) (σ y)
       grind)
    | (have r₁ := eq1958
       have r₂ := eq41 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq1958
       have r₂ := eq41 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq1958 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2040 : (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq2039
  have eq2221 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1801
       grind)
    | exact superpose eq1801 eq16
    | exact resolve eq16 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq2222 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq2221
       have r₂ := eq91 x
       grind)
    | exact resolve eq2221 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2224 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq2222
       grind)
    | exact superpose eq2222 eq9
    | exact resolve eq9 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2267 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq2224
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2224
    | exact resolve eq2224 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2269 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2267
       grind)
    | exact superpose eq2267 eq16
    | exact resolve eq16 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2270 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq2269
       have r₂ := eq91 x
       grind)
    | exact resolve eq2269 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2358 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq2270
       grind)
    | exact superpose eq2270 eq9
    | exact resolve eq9 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2402 : x = (k y x) := by
    first
    | (have i₁ := eq2358
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2358
    | exact resolve eq2358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358
  have eq3079 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2040
       have i₂ := eq2402
       grind)
    | exact superpose eq2402 eq2040
    | exact resolve eq2040 eq2402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040 eq2402
  have eq3080 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1958
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq1958
    | exact resolve eq1958 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq3079
  have eq3094 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3080
  have eq3095 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3094
  have eq3096 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3095
       grind)
    | exact superpose eq3095 eq16
    | exact resolve eq16 eq3095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3101 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3096
       have r₂ := eq91 x
       grind)
    | exact resolve eq3096 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3096
  have eq3103 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq3101
       grind)
    | exact superpose eq3101 eq9
    | exact resolve eq9 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq3154 : x = y := by
    first
    | (have i₁ := eq3103
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3103
    | exact resolve eq3103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq3286 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3154
       grind)
    | exact superpose eq3154 eq16
    | exact resolve eq16 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq3291 : False := by grind
  exact eq3291

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then Y else if m(Y,X) = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pyx_y_pyx_y_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41 (σ y) (σ x)
       grind)
    | exact superpose eq41 eq16
    | (have j1 := eq41 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq41 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq41 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq41 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq41 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq58 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq58 (M.op X0 X1) (M.op X0 X0)
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq58 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq54
    | exact resolve eq54 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq77 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq24 (τ X0)
       grind)
    | exact superpose eq24 eq19
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq80
    | exact resolve eq80 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq80
  have eq91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq88 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq60
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq60
    | (have j1 := eq41 (M.op (σ x) (σ y)) (σ (k y x))
       grind)
    | (have r₁ := eq60
       have r₂ := eq41 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq60
       have r₂ := eq41 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq60 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq99
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq59 X0 (τ X1)
       grind)
    | exact superpose eq59 eq18
    | (have j1 := eq59 X0 (τ X1)
       grind)
    | exact resolve eq18 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq108 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq59 (τ X0) X1
       grind)
    | exact superpose eq59 eq19
    | (have j1 := eq59 (τ X0) X1
       grind)
    | exact resolve eq19 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq257 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq105
    | exact resolve eq105 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq279 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq257 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq257
    | (have j0 := eq257 X0 X1
       grind)
    | exact resolve eq257 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq289 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq19
    | (have j1 := eq108 X0 X1
       grind)
    | exact resolve eq19 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq108
  have eq298 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq289
    | (have j0 := eq289 X0 X1
       grind)
    | exact resolve eq289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq345 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq346 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq345
       have r₂ := eq91 x
       grind)
    | exact resolve eq345 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq403 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 y x
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 y x
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1292 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq298 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq298
    | (have j0 := eq298 (σ X0) X1
       grind)
    | exact resolve eq298 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1330 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1292 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1292
    | (have j0 := eq1292 X0 X1
       grind)
    | exact resolve eq1292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1334 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1330 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1330
    | (have j0 := eq1330 X0 X1
       grind)
    | exact resolve eq1330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq403
       have i₂ := eq346
       grind)
    | exact superpose eq346 eq403
    | exact resolve eq403 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq403
  have eq1711 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq1710
  have eq1712 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq1711
  have eq1713 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1712
       have r₂ := eq60
       grind)
    | exact resolve eq1712 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1712
  have eq1715 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1713
       grind)
    | exact superpose eq1713 eq16
    | exact resolve eq16 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq1797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq1715
       have i₂ := eq1334 x y
       grind)
    | exact superpose eq1334 eq1715
    | (have j1 := eq1334 x y
       grind)
    | (have r₁ := eq1715
       have r₂ := eq1334 x y
       grind)
    | (have r₁ := eq1715
       have r₂ := eq1334 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1715
       have r₂ := eq1334 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1715 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1799 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq1715
       have i₂ := eq279 y x
       grind)
    | exact superpose eq279 eq1715
    | (have j1 := eq279 y x
       grind)
    | (have r₁ := eq1715
       have r₂ := eq279 y x
       grind)
    | (have r₁ := eq1715
       have r₂ := eq279 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1715
       have r₂ := eq279 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1715 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq1800 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq1799
  have eq1801 : x = y ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq1797
  have eq1878 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1800
       grind)
    | exact superpose eq1800 eq16
    | exact resolve eq16 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1879 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1878
       have r₂ := eq91 x
       grind)
    | exact resolve eq1878 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq1955 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1715
       have i₂ := eq1879
       grind)
    | exact superpose eq1879 eq1715
    | exact resolve eq1715 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715 eq1879
  have eq1958 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq1955
  have eq2039 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1958
       have i₂ := eq41 y x
       grind)
    | exact superpose eq41 eq1958
    | (have j1 := eq41 (σ x) (σ y)
       grind)
    | (have r₁ := eq1958
       have r₂ := eq41 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq1958
       have r₂ := eq41 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq1958 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2040 : (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq2039
  have eq2221 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1801
       grind)
    | exact superpose eq1801 eq16
    | exact resolve eq16 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq2222 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq2221
       have r₂ := eq91 x
       grind)
    | exact resolve eq2221 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2224 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq2222
       grind)
    | exact superpose eq2222 eq9
    | exact resolve eq9 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2267 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq2224
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2224
    | exact resolve eq2224 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2269 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2267
       grind)
    | exact superpose eq2267 eq16
    | exact resolve eq16 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq2270 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq2269
       have r₂ := eq91 x
       grind)
    | exact resolve eq2269 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2358 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq2270
       grind)
    | exact superpose eq2270 eq9
    | exact resolve eq9 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2402 : x = (k y x) := by
    first
    | (have i₁ := eq2358
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2358
    | exact resolve eq2358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358
  have eq3079 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2040
       have i₂ := eq2402
       grind)
    | exact superpose eq2402 eq2040
    | exact resolve eq2040 eq2402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040 eq2402
  have eq3080 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1958
       have i₂ := eq3079
       grind)
    | exact superpose eq3079 eq1958
    | exact resolve eq1958 eq3079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq3079
  have eq3094 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3080
  have eq3095 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3094
  have eq3096 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3095
       grind)
    | exact superpose eq3095 eq16
    | exact resolve eq16 eq3095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3101 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3096
       have r₂ := eq91 x
       grind)
    | exact resolve eq3096 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3096
  have eq3103 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq3101
       grind)
    | exact superpose eq3101 eq9
    | exact resolve eq9 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq3154 : x = y := by
    first
    | (have i₁ := eq3103
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3103
    | exact resolve eq3103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3103
  have eq3286 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3154
       grind)
    | exact superpose eq3154 eq16
    | exact resolve eq16 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq3291 : False := by grind
  exact eq3291

/-- `x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_pxx_pyy_pyx_pyy_pyy_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq50 (σ X0)
       grind)
    | exact superpose eq50 eq10
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq50 x
       grind)
    | exact superpose eq50 eq43
    | exact resolve eq43 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq54 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq53
       have i₂ := eq50 sF2
       grind)
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq66 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq50 sF2
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq67 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq66
       have i₂ := eq50 x
       grind)
    | exact superpose eq50 eq66
    | exact resolve eq66 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq73
    | (have j0 := eq73 (σ X0) (σ X1)
       grind)
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq50 sF3
       grind)
    | exact superpose eq50 eq90
    | exact resolve eq90 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq50 y
       grind)
    | exact superpose eq50 eq94
    | exact resolve eq94 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq94
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq89
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq89 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq114 : (M.op x y) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
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
  have eq115 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq55 X1
       grind)
    | exact superpose eq55 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq532 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq531
    | (have j0 := eq531 X0 X1
       grind)
    | exact resolve eq531 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq531
  have eq640 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (σ (M.op y y)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq532 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq532
    | (have j0 := eq532 y X0
       grind)
    | exact resolve eq532 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq671 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq640 X0
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq640
    | (have j0 := eq640 X0
       grind)
    | exact resolve eq640 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq3311 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq671 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq671
    | (have j0 := eq671 x
       grind)
    | exact resolve eq671 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq3318 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3311
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq3311
    | exact resolve eq3311 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq3338 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq3318
    | exact resolve eq3318 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq3346 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3338
       have i₂ := eq54
       grind)
    | exact superpose eq54 eq3338
    | exact resolve eq3338 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3352 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq3346
    | exact resolve eq3346 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq3358 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq3352
    | exact resolve eq3352 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq20852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq107 eq73
    | (have j0 := eq73 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20853 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20852
    | exact resolve eq20852 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20852
  have eq20864 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq20853
       have r₂ := eq27
       grind)
    | exact resolve eq20853 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20853
  have eq20868 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20864
    | exact resolve eq20864 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20864
  have eq20870 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20868
    | exact resolve eq20868 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20868
  have eq20884 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20870 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq20870
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq20870
       grind)
    | exact resolve eq14 eq20870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20870
  have eq25528 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20884
    | (have j0 := eq20884 (σ x)
       grind)
    | (have r₁ := eq20884 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq20884 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20884
  have eq25532 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq25528
  have eq25659 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq25532 eq103
    | exact resolve eq103 eq25532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25532
  have eq25685 : (M.op x x) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq67 eq25659
    | exact resolve eq25659 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq25659
  have eq25884 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq73 y x
       have i₂ := eq25685
       grind)
    | exact superpose eq25685 eq73
    | (have j0 := eq73 y x
       grind)
    | exact resolve eq73 eq25685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25685
  have eq25885 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq25884
  have eq25888 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq25885
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25885
    | exact resolve eq25885 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25885
  have eq25889 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq25888
  have eq25903 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq25889
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25889
    | exact resolve eq25889 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25889
  have eq25904 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq25903
  have eq26151 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq25904 eq115
    | (have r₁ := eq115
       have r₂ := eq25904
       grind)
    | exact resolve eq115 eq25904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26168 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq26151
  have eq26169 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq26168
  have eq34333 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26169 eq103
    | exact resolve eq103 eq26169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq26169
  have eq34364 : (M.op y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq122 eq34333
    | exact resolve eq34333 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq34333
  have eq35029 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq73 y x
       have i₂ := eq34364
       grind)
    | exact superpose eq34364 eq73
    | (have j0 := eq73 y x
       grind)
    | exact resolve eq73 eq34364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq34364
  have eq35030 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq35029
  have eq35035 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq35030
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35030
    | exact resolve eq35030 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35030
  have eq35036 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq35035
  have eq35050 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq35036
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35036
    | exact resolve eq35036 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35036
  have eq35051 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq35050
  have eq35068 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq35051 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq35051
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq35051
       grind)
    | exact resolve eq14 eq35051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35051
  have eq49360 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq35068
    | (have j0 := eq35068 (σ x)
       grind)
    | (have r₁ := eq35068 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq35068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35068
  have eq49370 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq49360
  have eq49383 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq49370 eq107
    | exact resolve eq107 eq49370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq49370
  have eq49400 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq49383
  have eq49740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq49400 eq25904
    | exact resolve eq25904 eq49400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25904 eq49400
  have eq49808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq49740
  have eq49814 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq49808
       have r₂ := eq27
       grind)
    | exact resolve eq49808 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49808
  have eq49831 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq49814
       grind)
    | exact superpose eq49814 eq96
    | exact resolve eq96 eq49814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49844 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq49814
       grind)
    | exact superpose eq49814 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq49814
       grind)
    | exact resolve eq14 eq49814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49814
  have eq49864 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq49831
    | exact resolve eq49831 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49831
  have eq67375 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq49844 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq49844
    | (have j0 := eq49844 x
       grind)
    | (have r₁ := eq49844 x
       have r₂ := eq18
       grind)
    | exact resolve eq49844 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49844
  have eq67385 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq67375
  have eq67390 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq67385
       grind)
    | exact superpose eq67385 eq89
    | exact resolve eq89 eq67385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67402 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq665 x y
       have i₂ := eq67385
       grind)
    | exact superpose eq67385 eq665
    | (have j0 := eq665 x y
       grind)
    | exact resolve eq665 eq67385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67385
  have eq67405 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq67402
  have eq67411 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq67405
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq67405
    | exact resolve eq67405 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67405
  have eq67422 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq67390
       have i₂ := eq54
       grind)
    | exact superpose eq54 eq67390
    | exact resolve eq67390 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67390
  have eq67426 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq67411
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq67411
    | exact resolve eq67411 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67411
  have eq67428 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq67426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq67426
    | exact resolve eq67426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67426
  have eq67429 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq67428
    | exact resolve eq67428 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67428
  have eq67430 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq67429
       have i₂ := eq54
       grind)
    | exact superpose eq54 eq67429
    | exact resolve eq67429 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67429
  have eq67431 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq67430
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq67430
    | exact resolve eq67430 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67430
  have eq67432 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq67431
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq67431
    | exact resolve eq67431 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67431
  have eq67433 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq67432
    | exact resolve eq67432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67432
  have eq67497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq67433 eq49864
    | exact resolve eq49864 eq67433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq67497
  have eq67560 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq67546
       have r₂ := eq27
       grind)
    | exact resolve eq67546 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67546
  have eq67881 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq67560 eq115
    | (have r₁ := eq115
       have r₂ := eq67560
       grind)
    | exact resolve eq115 eq67560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq67560
  have eq67915 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq67881
  have eq67916 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq67915
  have eq80439 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq67916 eq67422
    | exact resolve eq67422 eq67916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67422 eq67916
  have eq80444 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq80439
  have eq80892 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq80444
  have eq80977 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq80892
       have r₂ := eq67433
       grind)
    | exact resolve eq80892 eq67433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67433 eq80892
  have eq81012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq80977 eq49864
    | exact resolve eq49864 eq80977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49864 eq80977
  have eq81065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq81012
  have eq81081 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq81065
       have r₂ := eq27
       grind)
    | exact resolve eq81065 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81065
  have eq81086 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq81081
       grind)
    | exact superpose eq81081 eq54
    | exact resolve eq54 eq81081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81088 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq81081
       grind)
    | exact superpose eq81081 eq114
    | (have r₁ := eq114
       have r₂ := eq81081
       grind)
    | exact resolve eq114 eq81081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq81108 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
  clear eq81088
  have eq81109 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq81108
  have eq81125 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq81086
    | exact resolve eq81086 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81086
  have eq81869 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq81109
       grind)
    | exact superpose eq81109 eq89
    | exact resolve eq89 eq81109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq81109
  have eq81914 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq81869
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq81869
    | exact resolve eq81869 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81869
  have eq81953 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq81914 eq3358
    | exact resolve eq3358 eq81914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq81971 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq81953
  have eq81981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq81125 eq81971
    | exact resolve eq81971 eq81125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81971
  have eq81994 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq81981
       have r₂ := eq27
       grind)
    | exact resolve eq81981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81981
  have eq82049 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq81994 eq14
    | (have j0 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq81994
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq81994
       grind)
    | exact resolve eq14 eq81994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111953 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq82049
    | (have j0 := eq82049 (σ x)
       grind)
    | (have r₁ := eq82049 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq82049 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82049
  have eq111972 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq111953
  have eq111974 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq81125 eq111972
    | exact resolve eq111972 eq81125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111972
  have eq112014 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq111974 eq81914
    | exact resolve eq81914 eq111974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81914 eq111974
  have eq112017 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq112014
  have eq112134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq112017 eq81994
    | exact resolve eq81994 eq112017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81994 eq112017
  have eq112198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq112134
  have eq112257 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq112198
       have r₂ := eq27
       grind)
    | exact resolve eq112198 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112198
  have eq112275 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq112257
       grind)
    | exact superpose eq112257 eq96
    | exact resolve eq96 eq112257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112298 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0
       have i₂ := eq112257
       grind)
    | exact superpose eq112257 eq14
    | (have j0 := eq14 y X0
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq112257
       grind)
    | exact resolve eq14 eq112257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112257
  have eq112323 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq112275
    | exact resolve eq112275 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112275
  have eq117778 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq112298 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112298
    | (have j0 := eq112298 x
       grind)
    | (have r₁ := eq112298 x
       have r₂ := eq18
       grind)
    | exact resolve eq112298 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq112298
  have eq117787 : (M.op x x) = (k y x) := by grind
  clear eq117778
  have eq117789 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq117787
       have i₂ := eq81081
       grind)
    | exact superpose eq81081 eq117787
    | exact resolve eq117787 eq81081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81081 eq117787
  have eq118536 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq665 x y
       have i₂ := eq117789
       grind)
    | exact superpose eq117789 eq665
    | (have j0 := eq665 x y
       grind)
    | exact resolve eq665 eq117789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq117789
  have eq118546 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq118536
       have i₂ := eq54
       grind)
    | exact superpose eq54 eq118536
    | exact resolve eq118536 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq118536
  have eq118561 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq81125 eq118546
    | (have r₁ := eq118546
       have r₂ := eq81125
       grind)
    | exact resolve eq118546 eq81125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81125 eq118546
  have eq118564 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq118561
       have r₂ := eq20
       grind)
    | exact resolve eq118561 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118561
  have eq118565 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq118564
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq118564
    | exact resolve eq118564 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq118564
  have eq118566 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq112323 eq118565
    | exact resolve eq118565 eq112323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112323 eq118565
  have eq118567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq118566
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq118566
    | exact resolve eq118566 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118566
  have eq118568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq118567
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118567
    | exact resolve eq118567 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118567
  have eq118569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq118568
    | exact resolve eq118568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118568
  have eq118570 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq118569
       have r₂ := eq27
       grind)
    | exact resolve eq118569 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118569
  have eq118571 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq118570
    | exact resolve eq118570 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq118570
  have eq118572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq118571
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq118571
    | exact resolve eq118571 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq118571
  have eq118573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq118572
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq118572
    | exact resolve eq118572 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118572
  have eq118574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq118573
    | exact resolve eq118573 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq118573
  have eq118575 : False := by grind
  exact eq118575

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else if X = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_pxy_x_x_y_pxy_x_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq52 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq56 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq96 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq104 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq96 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq96 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq96 (σ X0) (M.op X0 X0)
       have r₂ := eq46 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq96 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq96
  have eq329 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104
    | exact resolve eq104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq104 (σ X1) X0
       grind)
    | exact superpose eq104 eq15
    | (have j1 := eq104 (σ X1) X0
       grind)
    | exact resolve eq15 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq453 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq486 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq453
    | (have j0 := eq453 X0 X1
       grind)
    | exact resolve eq453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq555 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq329 X0 (τ X1)
       grind)
    | exact superpose eq329 eq19
    | (have j1 := eq329 (M.op X0 (τ X1)) X0
       grind)
    | exact resolve eq19 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3428 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq336 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq4163 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq486 X1 X0
       grind)
    | exact superpose eq486 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq486 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq486 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq486 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq486 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq4172 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4163 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4163
  have eq4173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172
  have eq5271 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq555
    | exact resolve eq555 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq5291 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5271 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5271
    | (have j0 := eq5271 X0 X1
       grind)
    | exact resolve eq5271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq6905 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq4173 X0 X1
       grind)
    | exact superpose eq4173 eq9
    | (have j1 := eq4173 X0 X1
       grind)
    | exact resolve eq9 eq4173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173
  have eq6981 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6905 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq6905
    | (have j0 := eq6905 X0 X1
       grind)
    | exact resolve eq6905 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6905
  have eq7004 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6981 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq6981 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq6981 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq6981 (M.op X0 X0) (M.op X1 X0)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq6981 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6981
  have eq7036 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq7004 X0 (σ X1)
       grind)
    | exact superpose eq7004 eq29
    | (have j1 := eq7004 (k X0 (σ X1)) X0
       grind)
    | exact resolve eq29 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq7136 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7004 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7225 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7136 X0 X1
       have i₂ := eq5291 X1 X0
       grind)
    | exact superpose eq5291 eq7136
    | (have j0 := eq7136 X0 X1
       have j1 := eq5291 X1 X0
       grind)
    | (have r₁ := eq7136 X1 X0
       have r₂ := eq5291 X0 X1
       grind)
    | (have r₁ := eq7136 X1 X1
       have r₂ := eq5291 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq7136 X0 X1
       have r₂ := eq5291 X0 (M.op X0 X1)
       grind)
    | exact resolve eq7136 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291 eq7136
  have eq7295 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7225 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7225
  have eq7296 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7295
  have eq7575 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq7036 (σ X0) X1
       grind)
    | exact superpose eq7036 eq38
    | (have j1 := eq7036 (σ X1) X0
       grind)
    | exact resolve eq38 eq7036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7036
  have eq7660 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7575 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq7575
    | (have j0 := eq7575 X0 X1
       grind)
    | exact resolve eq7575 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7575
  have eq7695 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7660 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7660
    | (have j0 := eq7660 X0 X1
       grind)
    | exact resolve eq7660 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7660
  have eq7706 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7695 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7695
    | (have j0 := eq7695 X0 X1
       grind)
    | exact resolve eq7695 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695
  have eq8027 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7706 (τ X1) (τ X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq7706
    | (have j0 := eq7706 (τ X0) (τ X1)
       grind)
    | exact resolve eq7706 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq7706
  have eq8264 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8027 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8027
    | (have j0 := eq8027 X0 X1
       grind)
    | exact resolve eq8027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8027
  have eq8341 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8264 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8264
    | (have j0 := eq8264 X0 X1
       grind)
    | exact resolve eq8264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8264
  have eq8402 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8341 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8341
    | (have j0 := eq8341 X0 X1
       grind)
    | exact resolve eq8341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8341
  have eq8460 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8402 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8402
    | (have j0 := eq8402 X0 X1
       grind)
    | exact resolve eq8402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402
  have eq8578 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq8460 X0 X1
       grind)
    | exact superpose eq8460 eq10
    | (have j1 := eq8460 X0 X1
       grind)
    | exact resolve eq10 eq8460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8706 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8578 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq8578
    | (have j0 := eq8578 X0 X1
       grind)
    | exact resolve eq8578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8578
  have eq8897 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8706 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8706
    | (have j0 := eq8706 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq8706 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8706
  have eq9074 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8897 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq8897
    | (have j0 := eq8897 X0 X1
       grind)
    | exact resolve eq8897 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8897
  have eq9079 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9074 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq9074
    | (have j0 := eq9074 X0 X1
       grind)
    | exact resolve eq9074 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9074
  have eq10025 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9079 x y
       grind)
    | exact superpose eq9079 eq16
    | (have j1 := eq9079 x y
       grind)
    | exact resolve eq16 eq9079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9079
  have eq10238 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10025
       have i₂ := eq329 x y
       grind)
    | exact superpose eq329 eq10025
    | (have j1 := eq329 x y
       grind)
    | (have r₁ := eq10025
       have r₂ := eq329 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq10025
       have r₂ := eq329 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq10025 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq10240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq10025
       have i₂ := eq7296 x y
       grind)
    | exact superpose eq7296 eq10025
    | (have j1 := eq7296 x y
       grind)
    | (have r₁ := eq10025
       have r₂ := eq7296 x y
       grind)
    | (have r₁ := eq10025
       have r₂ := eq7296 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq10025
       have r₂ := eq7296 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq10025 eq7296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296 eq10025
  have eq10244 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq10240
  have eq10245 : x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq10244
  have eq10248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10238
  have eq10249 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10248
  have eq10251 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10245
       grind)
    | exact superpose eq10245 eq16
    | exact resolve eq16 eq10245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10245
  have eq10252 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10251
       have r₂ := eq23 x
       grind)
    | exact resolve eq10251 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10251
  have eq10313 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3428 x y
       have i₂ := eq10252
       grind)
    | exact superpose eq10252 eq3428
    | (have j0 := eq3428 x y
       grind)
    | exact resolve eq3428 eq10252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428 eq10252
  have eq10318 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10313
  have eq10319 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10318
  have eq10331 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10249
       grind)
    | exact superpose eq10249 eq16
    | exact resolve eq16 eq10249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10249
  have eq10332 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10331
       have r₂ := eq23 x
       grind)
    | exact resolve eq10331 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10331
  have eq10393 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10319
       grind)
    | exact superpose eq10319 eq16
    | exact resolve eq16 eq10319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10319
  have eq10463 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10393
       have i₂ := eq10332
       grind)
    | exact superpose eq10332 eq10393
    | exact resolve eq10393 eq10332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10332 eq10393
  have eq10479 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq10463
  have eq10480 : (σ x) = (σ y) := by grind
  clear eq10479
  have eq10481 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10480
       grind)
    | exact superpose eq10480 eq16
    | exact resolve eq16 eq10480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10482 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq10480
       grind)
    | exact superpose eq10480 eq9
    | exact resolve eq9 eq10480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10480
  have eq10563 : x = y := by
    first
    | (have i₁ := eq10482
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq10482
    | exact resolve eq10482 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10482
  have eq10564 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10481
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq10481
    | exact resolve eq10481 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10481
  have eq10565 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10564
       have i₂ := eq10563
       grind)
    | exact superpose eq10563 eq10564
    | exact resolve eq10564 eq10563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10563 eq10564
  have eq10566 : False := by grind
  exact eq10566

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else if X = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_pxy_x_x_y_pxy_x_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = a ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq20 (σ X0)
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq22
    | exact resolve eq22 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq52 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq56 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq96 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq104 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq96 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq96 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq96 (σ X0) (M.op X0 X0)
       have r₂ := eq46 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq96 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq96
  have eq329 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104
    | exact resolve eq104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq104 (σ X1) X0
       grind)
    | exact superpose eq104 eq15
    | (have j1 := eq104 (σ X1) X0
       grind)
    | exact resolve eq15 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq453 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq486 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq453
    | (have j0 := eq453 X0 X1
       grind)
    | exact resolve eq453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq555 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq329 X0 (τ X1)
       grind)
    | exact superpose eq329 eq19
    | (have j1 := eq329 (M.op X0 (τ X1)) X0
       grind)
    | exact resolve eq19 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3428 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq336 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq4163 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq486 X1 X0
       grind)
    | exact superpose eq486 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq486 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq486 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq486 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq486 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq4172 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4163 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4163
  have eq4173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172
  have eq5271 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq555
    | exact resolve eq555 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq5291 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5271 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5271
    | (have j0 := eq5271 X0 X1
       grind)
    | exact resolve eq5271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq6905 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq4173 X0 X1
       grind)
    | exact superpose eq4173 eq9
    | (have j1 := eq4173 X0 X1
       grind)
    | exact resolve eq9 eq4173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173
  have eq6981 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6905 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq6905
    | (have j0 := eq6905 X0 X1
       grind)
    | exact resolve eq6905 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6905
  have eq7004 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6981 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq6981 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq6981 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq6981 (M.op X0 X0) (M.op X1 X0)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq6981 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6981
  have eq7036 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq7004 X0 (σ X1)
       grind)
    | exact superpose eq7004 eq29
    | (have j1 := eq7004 (k X0 (σ X1)) X0
       grind)
    | exact resolve eq29 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq7136 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7004 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7225 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7136 X0 X1
       have i₂ := eq5291 X1 X0
       grind)
    | exact superpose eq5291 eq7136
    | (have j0 := eq7136 X0 X1
       have j1 := eq5291 X1 X0
       grind)
    | (have r₁ := eq7136 X1 X0
       have r₂ := eq5291 X0 X1
       grind)
    | (have r₁ := eq7136 X1 X1
       have r₂ := eq5291 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq7136 X0 X1
       have r₂ := eq5291 X0 (M.op X0 X1)
       grind)
    | exact resolve eq7136 eq5291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5291 eq7136
  have eq7295 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7225 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7225
  have eq7296 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7295
  have eq7575 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq7036 (σ X0) X1
       grind)
    | exact superpose eq7036 eq38
    | (have j1 := eq7036 (σ X1) X0
       grind)
    | exact resolve eq38 eq7036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7036
  have eq7660 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7575 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq7575
    | (have j0 := eq7575 X0 X1
       grind)
    | exact resolve eq7575 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7575
  have eq7695 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7660 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7660
    | (have j0 := eq7660 X0 X1
       grind)
    | exact resolve eq7660 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7660
  have eq7706 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7695 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq7695
    | (have j0 := eq7695 X0 X1
       grind)
    | exact resolve eq7695 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695
  have eq8027 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7706 (τ X1) (τ X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq7706
    | (have j0 := eq7706 (τ X0) (τ X1)
       grind)
    | exact resolve eq7706 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq7706
  have eq8264 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8027 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8027
    | (have j0 := eq8027 X0 X1
       grind)
    | exact resolve eq8027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8027
  have eq8341 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8264 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8264
    | (have j0 := eq8264 X0 X1
       grind)
    | exact resolve eq8264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8264
  have eq8402 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8341 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8341
    | (have j0 := eq8341 X0 X1
       grind)
    | exact resolve eq8341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8341
  have eq8460 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8402 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8402
    | (have j0 := eq8402 X0 X1
       grind)
    | exact resolve eq8402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402
  have eq8578 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq8460 X0 X1
       grind)
    | exact superpose eq8460 eq10
    | (have j1 := eq8460 X0 X1
       grind)
    | exact resolve eq10 eq8460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8706 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8578 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq8578
    | (have j0 := eq8578 X0 X1
       grind)
    | exact resolve eq8578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8578
  have eq8897 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8706 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8706
    | (have j0 := eq8706 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq8706 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8706
  have eq9074 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8897 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq8897
    | (have j0 := eq8897 X0 X1
       grind)
    | exact resolve eq8897 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8897
  have eq9079 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9074 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq9074
    | (have j0 := eq9074 X0 X1
       grind)
    | exact resolve eq9074 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9074
  have eq10025 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9079 x y
       grind)
    | exact superpose eq9079 eq16
    | (have j1 := eq9079 x y
       grind)
    | exact resolve eq16 eq9079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9079
  have eq10238 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10025
       have i₂ := eq329 x y
       grind)
    | exact superpose eq329 eq10025
    | (have j1 := eq329 x y
       grind)
    | (have r₁ := eq10025
       have r₂ := eq329 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq10025
       have r₂ := eq329 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq10025 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq10240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq10025
       have i₂ := eq7296 x y
       grind)
    | exact superpose eq7296 eq10025
    | (have j1 := eq7296 x y
       grind)
    | (have r₁ := eq10025
       have r₂ := eq7296 x y
       grind)
    | (have r₁ := eq10025
       have r₂ := eq7296 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq10025
       have r₂ := eq7296 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq10025 eq7296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296 eq10025
  have eq10244 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq10240
  have eq10245 : x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq10244
  have eq10248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10238
  have eq10249 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10248
  have eq10251 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10245
       grind)
    | exact superpose eq10245 eq16
    | exact resolve eq16 eq10245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10245
  have eq10252 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10251
       have r₂ := eq23 x
       grind)
    | exact resolve eq10251 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10251
  have eq10313 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3428 x y
       have i₂ := eq10252
       grind)
    | exact superpose eq10252 eq3428
    | (have j0 := eq3428 x y
       grind)
    | exact resolve eq3428 eq10252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428 eq10252
  have eq10318 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10313
  have eq10319 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10318
  have eq10331 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10249
       grind)
    | exact superpose eq10249 eq16
    | exact resolve eq16 eq10249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10249
  have eq10332 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10331
       have r₂ := eq23 x
       grind)
    | exact resolve eq10331 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10331
  have eq10393 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10319
       grind)
    | exact superpose eq10319 eq16
    | exact resolve eq16 eq10319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10319
  have eq10463 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10393
       have i₂ := eq10332
       grind)
    | exact superpose eq10332 eq10393
    | exact resolve eq10393 eq10332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10332 eq10393
  have eq10479 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq10463
  have eq10480 : (σ x) = (σ y) := by grind
  clear eq10479
  have eq10481 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10480
       grind)
    | exact superpose eq10480 eq16
    | exact resolve eq16 eq10480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10482 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq10480
       grind)
    | exact superpose eq10480 eq9
    | exact resolve eq9 eq10480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10480
  have eq10563 : x = y := by
    first
    | (have i₁ := eq10482
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq10482
    | exact resolve eq10482 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10482
  have eq10564 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10481
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq10481
    | exact resolve eq10481 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10481
  have eq10565 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10564
       have i₂ := eq10563
       grind)
    | exact superpose eq10563 eq10564
    | exact resolve eq10564 eq10563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10563 eq10564
  have eq10566 : False := by grind
  exact eq10566

/-- `x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_pyx_pyy_pxy_pyx_pyy_pxx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq15
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq51 (τ X0)
       grind)
    | exact superpose eq51 eq18
    | exact resolve eq18 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq59
    | exact resolve eq59 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq59
  have eq71 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq11
    | (have j0 := eq11 (σ X0) X1
       grind)
    | exact resolve eq11 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0))
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq295 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq282
    | (have j0 := eq282 X0 X1
       grind)
    | exact resolve eq282 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq304 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | exact resolve eq295 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq470 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq304 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq304 X0 X1
       grind)
    | exact superpose eq304 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq304 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq304 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq304 X0 X1
       grind)
    | exact resolve eq13 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq484 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq470 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq493 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq484 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq484
    | (have j0 := eq484 X0 X1
       grind)
    | exact resolve eq484 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq494 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq509 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 X1
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq494
    | (have j0 := eq494 X0 X1
       grind)
    | exact resolve eq494 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq510 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq509 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq520 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq510
    | (have j0 := eq510 X0 X1
       grind)
    | exact resolve eq510 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq521 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq617 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq521 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq521
    | exact resolve eq521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq521 x y
       grind)
    | exact superpose eq521 eq16
    | (have j1 := eq521 x y
       grind)
    | exact resolve eq16 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq521 X1 X0
       grind)
    | exact superpose eq521 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq521 X1 X0
       grind)
    | exact resolve eq11 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq669 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq645 X0 X1
       grind)
    | (have r₁ := eq645 X0 X1
       have r₂ := eq62 X0
       grind)
    | exact resolve eq645 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq678 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq617 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq617
    | (have j0 := eq617 X0 X1
       grind)
    | exact resolve eq617 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq685 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq692 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq678
    | (have j0 := eq678 X0 X1
       grind)
    | exact resolve eq678 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq698 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq685
    | (have j0 := eq685 X0 X1
       grind)
    | exact resolve eq685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq12417 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq692
    | exact resolve eq692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq12627 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12417 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12417
    | (have j0 := eq12417 X0 X1
       grind)
    | exact resolve eq12417 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12417
  have eq12649 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12627 X1 (τ X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12627
    | (have j0 := eq12627 X1 (τ X0)
       grind)
    | exact resolve eq12627 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12689 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12627 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12627 X0 X1
       grind)
    | exact superpose eq12627 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12627 X1 X0
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12627 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12627 X1 X1
       grind)
    | exact resolve eq11 eq12627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12627
  have eq12701 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12689 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12689
  have eq12749 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12701 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq12701
    | (have j0 := eq12701 (τ X0) (τ X1)
       grind)
    | exact resolve eq12701 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12847 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq12701 (σ X1) X0
       grind)
    | exact superpose eq12701 eq28
    | (have j1 := eq12701 (σ X1) X0
       grind)
    | exact resolve eq28 eq12701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12882 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12701 (τ X1) X0
       grind)
    | exact superpose eq12701 eq17
    | (have j1 := eq12701 (τ X1) X0
       grind)
    | exact resolve eq17 eq12701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12701
  have eq13156 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12749 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq12749
    | (have j0 := eq12749 X0 X1
       grind)
    | exact resolve eq12749 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12749
  have eq13257 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13156 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq13156
    | (have j0 := eq13156 X0 X1
       grind)
    | exact resolve eq13156 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13156
  have eq16521 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq662 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq662
    | (have j0 := eq662 (τ X1) (τ X0)
       grind)
    | exact resolve eq662 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16630 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16521 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq16521
    | (have j0 := eq16521 X0 X1
       grind)
    | exact resolve eq16521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16521
  have eq16686 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16630 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq16630
    | (have j0 := eq16630 X0 X1
       grind)
    | exact resolve eq16630 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16630
  have eq16730 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16686 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16686
    | (have j0 := eq16686 X0 X1
       grind)
    | exact resolve eq16686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16686
  have eq16767 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16730 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq16730
    | (have j0 := eq16730 X0 X1
       grind)
    | exact resolve eq16730 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16730
  have eq16777 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16767 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq16767
    | (have j0 := eq16767 X0 X1
       grind)
    | exact resolve eq16767 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16767
  have eq16786 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16777 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16777
    | (have j0 := eq16777 X0 X1
       grind)
    | exact resolve eq16777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16777
  have eq16795 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16786 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq16786
    | (have j0 := eq16786 X0 X1
       grind)
    | exact resolve eq16786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16786
  have eq16804 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16795 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq16795
    | (have j0 := eq16795 X0 X1
       grind)
    | exact resolve eq16795 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16795
  have eq17048 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 (σ X0)
       have i₂ := eq698 X1 X0
       grind)
    | exact superpose eq698 eq71
    | (have j0 := eq71 X1 (σ X0)
       have j1 := eq698 X1 X0
       grind)
    | (have r₁ := eq71 X0 (σ X0)
       have r₂ := eq698 X0 X0
       grind)
    | exact resolve eq71 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq17211 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17048 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq17048
    | (have j0 := eq17048 X0 X1
       grind)
    | exact resolve eq17048 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17048
  have eq17248 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17211 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17211
    | (have j0 := eq17211 X0 X1
       grind)
    | exact resolve eq17211 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17211
  have eq17249 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq17248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17248
  have eq23416 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12649 X1 X0
       grind)
    | exact superpose eq12649 eq17
    | (have j1 := eq12649 X1 X0
       grind)
    | exact resolve eq17 eq12649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12649
  have eq25969 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12847 (σ X0) X1
       grind)
    | exact superpose eq12847 eq15
    | (have j1 := eq12847 (σ X0) X1
       grind)
    | exact resolve eq15 eq12847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12847
  have eq26191 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25969 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq25969
    | (have j0 := eq25969 X0 X1
       grind)
    | exact resolve eq25969 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25969
  have eq26295 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (τ (σ X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26191 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq26191
    | (have j0 := eq26191 X0 X1
       grind)
    | exact resolve eq26191 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26191
  have eq26356 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26295 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq26295
    | (have j0 := eq26295 X0 X1
       grind)
    | exact resolve eq26295 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26295
  have eq26402 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26356 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq26356
    | (have j0 := eq26356 X0 X1
       grind)
    | exact resolve eq26356 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26356
  have eq27081 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12882 X0 X1
       grind)
    | exact superpose eq12882 eq17
    | (have j1 := eq12882 X0 X1
       grind)
    | exact resolve eq17 eq12882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27107 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12882 (τ X0) X1
       grind)
    | exact superpose eq12882 eq31
    | (have j1 := eq12882 (τ X0) X1
       grind)
    | exact resolve eq31 eq12882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12882
  have eq27333 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X0))) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27107 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq27107
    | (have j0 := eq27107 X0 X1
       grind)
    | exact resolve eq27107 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27107
  have eq27443 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27333 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27333
    | (have j0 := eq27333 X0 X1
       grind)
    | exact resolve eq27333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27333
  have eq27502 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27443 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq27443
    | (have j0 := eq27443 X0 X1
       grind)
    | exact resolve eq27443 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27443
  have eq34948 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23416 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq23416
    | exact resolve eq23416 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23416
  have eq35149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34948 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34948
    | (have j0 := eq34948 X0 X1
       grind)
    | exact resolve eq34948 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34948
  have eq35150 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35149 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq35149
    | (have j0 := eq35149 X0 X1
       grind)
    | exact resolve eq35149 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35149
  have eq35151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35150 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq35150
    | (have j0 := eq35150 X0 X1
       grind)
    | exact resolve eq35150 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35150
  have eq42216 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26402 x y
       grind)
    | exact superpose eq26402 eq16
    | (have j1 := eq26402 x y
       grind)
    | exact resolve eq16 eq26402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42298 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26402 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42718 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq42216
       have i₂ := eq35151 y x
       grind)
    | exact superpose eq35151 eq42216
    | (have j1 := eq35151 y x
       grind)
    | (have r₁ := eq42216
       have r₂ := eq35151 y x
       grind)
    | exact resolve eq42216 eq35151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42216
  have eq42722 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq42718
  have eq42727 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq42722
       have r₂ := eq11 y x
       grind)
    | exact resolve eq42722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42722
  have eq42730 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42727
       grind)
    | exact superpose eq42727 eq16
    | exact resolve eq16 eq42727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44578 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27081 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq27081
    | (have j0 := eq27081 X1 (σ X0)
       grind)
    | exact resolve eq27081 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27081
  have eq44797 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44578 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44578
    | (have j0 := eq44578 X0 X1
       grind)
    | exact resolve eq44578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44578
  have eq44798 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44797 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44797
    | (have j0 := eq44797 X0 X1
       grind)
    | exact resolve eq44797 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44797
  have eq45112 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X1)
       have i₂ := eq44798 X0 X1
       grind)
    | exact superpose eq44798 eq9
    | (have j1 := eq44798 X0 X1
       grind)
    | exact resolve eq9 eq44798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44798
  have eq45359 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45112 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq45112
    | (have j0 := eq45112 X0 X1
       grind)
    | exact resolve eq45112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45112
  have eq46922 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27502
  have eq46996 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq46922 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46922
    | (have j0 := eq46922 (σ X1) (σ X0)
       grind)
    | exact resolve eq46922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46922
  have eq47164 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq46996 X0 X1
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq46996
    | (have j0 := eq46996 X0 X1
       grind)
    | exact resolve eq46996 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46996
  have eq47228 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq47164 X0 X1
       have i₂ := eq9 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq47164
    | (have j0 := eq47164 X0 X1
       grind)
    | exact resolve eq47164 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47164
  have eq47263 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq47228 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq47228
    | (have j0 := eq47228 X0 X1
       grind)
    | exact resolve eq47228 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47228
  have eq47291 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq47263 X0 X1
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq47263
    | (have j0 := eq47263 X0 X1
       grind)
    | exact resolve eq47263 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47263
  have eq47312 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X1)) X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47291 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq47291
    | (have j0 := eq47291 X0 X1
       grind)
    | exact resolve eq47291 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47291
  have eq47331 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47312 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq47312
    | (have j0 := eq47312 X0 X1
       grind)
    | exact resolve eq47312 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47312
  have eq47345 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47331 X0 X1
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq47331
    | (have j0 := eq47331 X0 X1
       grind)
    | exact resolve eq47331 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47331
  have eq47354 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47345 X0 X1
       have i₂ := eq9 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq47345
    | (have j0 := eq47345 X0 X1
       grind)
    | exact resolve eq47345 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47345
  have eq84498 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17249 (τ X0) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq17249
    | (have j0 := eq17249 (τ X0) X1
       grind)
    | exact resolve eq17249 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17249
  have eq84546 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 (τ X0))) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84498 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq84498
    | (have j0 := eq84498 X0 X1
       grind)
    | exact resolve eq84498 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84498
  have eq84557 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 X0) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84546 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84546
    | (have j0 := eq84546 X0 X1
       grind)
    | exact resolve eq84546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84546
  have eq84566 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84557 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq84557
    | (have j0 := eq84557 X0 X1
       grind)
    | exact resolve eq84557 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq84557
  have eq84610 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (σ (τ X0)) X1) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84566 X1 (τ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq84566
    | (have j0 := eq84566 X1 (τ X0)
       grind)
    | (have r₁ := eq84566 X0 (τ X0)
       have r₂ := eq65 X0
       grind)
    | exact resolve eq84566 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84566
  have eq84620 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k (σ (τ X0)) X1) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84610 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84610
    | (have j0 := eq84610 X0 X1
       grind)
    | exact resolve eq84610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84610
  have eq84633 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq84620 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84620
    | (have j0 := eq84620 X0 X1
       grind)
    | exact resolve eq84620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84620
  have eq84652 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84633 (τ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq84633
    | (have j0 := eq84633 (τ X0) X1
       grind)
    | exact resolve eq84633 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84633
  have eq85116 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84652 X0 (τ X0)
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq84652
    | (have j0 := eq84652 X1 (τ X0)
       grind)
    | (have r₁ := eq84652 X0 (τ X0)
       have r₂ := eq83 X0
       grind)
    | exact resolve eq84652 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84652
  have eq85159 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85116 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq85116
    | (have j0 := eq85116 X0 X1
       grind)
    | exact resolve eq85116 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85116
  have eq85170 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85159 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq85159
    | (have j0 := eq85159 X0 X1
       grind)
    | exact resolve eq85159 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85159
  have eq122998 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X1) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1 (τ X0)
       have i₂ := eq13257 X0 X1
       grind)
    | exact superpose eq13257 eq106
    | (have j0 := eq106 X0 (τ X1)
       have j1 := eq13257 X1 X0
       grind)
    | (have r₁ := eq106 X1 (τ X0)
       have r₂ := eq13257 X0 X1
       grind)
    | exact resolve eq106 eq13257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq13257
  have eq123378 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X1) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq122998 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122998
  have eq123458 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123378 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq123378
    | (have j0 := eq123378 X0 X1
       grind)
    | exact resolve eq123378 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123378
  have eq123554 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X1)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq123458 X0 X1
       have j1 := eq85170 X0 X1
       grind)
    | (have r₁ := eq123458 X0 X1
       have r₂ := eq85170 X0 X1
       grind)
    | (have r₁ := eq123458 X1 X0
       have r₂ := eq85170 X0 X1
       grind)
    | exact resolve eq123458 eq85170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85170 eq123458
  have eq123624 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X1)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123554 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq123554
    | (have j0 := eq123554 X0 X1
       grind)
    | exact resolve eq123554 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq123554
  have eq123668 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123624 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq123624
    | (have j0 := eq123624 X0 X1
       grind)
    | exact resolve eq123624 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq123624
  have eq123738 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (M.op X0 (τ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k X1 (σ X0))) ∨ (τ (k X1 (σ X0))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123668 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq123668
    | (have j0 := eq123668 (σ X0) X1
       grind)
    | exact resolve eq123668 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123823 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ (k (σ X0) X1)) = (τ (M.op X1 X1)) ∨ (τ (k (σ X0) X1)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq123668 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq123668
    | (have j0 := eq123668 X1 (σ X0)
       grind)
    | exact resolve eq123668 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123668
  have eq124421 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (k (σ X0) X1)) = (τ (M.op X1 X1)) ∨ (τ (k (σ X0) X1)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq123823 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq123823
    | (have j0 := eq123823 X0 X1
       grind)
    | exact resolve eq123823 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123823
  have eq124427 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (k X1 (σ X0))) ∨ (τ (k X1 (σ X0))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123738 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq123738
    | (have j0 := eq123738 X0 X1
       grind)
    | exact resolve eq123738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123738
  have eq124549 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (k (σ X0) X1)) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq124421 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq124421
    | (have j0 := eq124421 X0 X1
       grind)
    | exact resolve eq124421 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124421
  have eq124554 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (τ (k X1 (σ X0))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124427 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq124427
    | (have j0 := eq124427 X0 X1
       grind)
    | exact resolve eq124427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124427
  have eq124629 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (τ (σ (M.op X0 X0))) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124549 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq124549
    | (have j0 := eq124549 X0 X1
       grind)
    | exact resolve eq124549 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124549
  have eq124634 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (σ (M.op X0 X0))) ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (τ (k X1 (σ X0))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124554 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq124554
    | (have j0 := eq124554 X0 X1
       grind)
    | exact resolve eq124554 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124554
  have eq124688 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) X1)) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124629 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq124629
    | (have j0 := eq124629 X0 X1
       grind)
    | exact resolve eq124629 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124629
  have eq124691 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (τ (k X1 (σ X0))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124634 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq124634
    | (have j0 := eq124634 X0 X1
       grind)
    | exact resolve eq124634 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124634
  have eq124725 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (k X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124688 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq124688
    | (have j0 := eq124688 X0 X1
       grind)
    | exact resolve eq124688 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124688
  have eq124726 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124691 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq124691
    | (have j0 := eq124691 X0 X1
       grind)
    | exact resolve eq124691 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq124691
  have eq124759 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124725 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq124725
    | exact resolve eq124725 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124725
  have eq125299 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124759 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq124759
    | (have j0 := eq124759 X0 X1
       grind)
    | exact resolve eq124759 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124759
  have eq125375 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq125299 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq125299
    | (have j0 := eq125299 X0 X1
       grind)
    | exact resolve eq125299 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125299
  have eq126052 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq125375 X1 (σ X0)
       grind)
    | exact superpose eq125375 eq28
    | (have j1 := eq125375 X1 (σ X0)
       grind)
    | exact resolve eq28 eq125375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq126123 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq125375 X1 (τ X0)
       grind)
    | exact superpose eq125375 eq17
    | (have j1 := eq125375 X1 (τ X0)
       grind)
    | exact resolve eq17 eq125375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq125375
  have eq126504 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126123 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq126123
    | (have j0 := eq126123 X0 X1
       grind)
    | exact resolve eq126123 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq126123
  have eq126570 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126052 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq126052
    | (have j0 := eq126052 X0 X1
       grind)
    | exact resolve eq126052 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126052
  have eq126905 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126570 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq126570
    | (have j0 := eq126570 X0 X1
       grind)
    | exact resolve eq126570 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126570
  have eq127609 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq126504 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126504
  have eq129689 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq127609 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq127609
    | (have j0 := eq127609 (σ X0) X1
       grind)
    | exact resolve eq127609 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127609
  have eq129808 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq129689 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq129689
    | (have j0 := eq129689 X0 X1
       grind)
    | exact resolve eq129689 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129689
  have eq129821 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq129808 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq129808
    | (have j0 := eq129808 X0 X1
       grind)
    | exact resolve eq129808 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129808
  have eq129851 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op (σ y) (σ y))) = (σ (k (σ y) (σ x))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq129821 (σ y) (σ x)
       have i₂ := eq42727
       grind)
    | exact superpose eq42727 eq129821
    | (have j0 := eq129821 (σ y) (σ x)
       grind)
    | (have r₁ := eq129821 y x
       have r₂ := eq42727
       grind)
    | exact resolve eq129821 eq42727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129821
  have eq129952 : (σ (M.op (σ y) (σ y))) = (σ (k (σ y) (σ x))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq129851
       have r₂ := eq62 x
       grind)
    | exact resolve eq129851 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129851
  have eq129988 : (σ (M.op (σ y) (σ y))) = (σ (σ (k y x))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq129952
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq129952
    | exact resolve eq129952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129952
  have eq130014 : (σ (σ (M.op y y))) = (σ (σ (k y x))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq129988
       have i₂ := eq62 y
       grind)
    | exact superpose eq62 eq129988
    | exact resolve eq129988 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129988
  have eq130036 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ (σ (M.op y y))) = (σ (σ (k y x))) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq130014
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq130014
    | exact resolve eq130014 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130014
  have eq130052 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ (σ (M.op y y))) = (σ (σ (k y x))) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq130036
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq130036
    | exact resolve eq130036 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130036
  have eq130066 : (σ (σ (M.op y y))) = (σ (σ (k y x))) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq47354 y x
       grind)
    | (have r₁ := eq130052
       have r₂ := eq47354 y x
       grind)
    | exact resolve eq130052 eq47354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130052
  have eq130176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126905 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126905
    | (have j0 := eq126905 X0 (σ X1)
       grind)
    | exact resolve eq126905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130461 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (σ X0)) ∨ (M.op X0 X0) = (k X0 (τ X1)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq126905 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126905
  have eq130623 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq130176 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq130176
    | (have j0 := eq130176 X0 X1
       grind)
    | exact resolve eq130176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130176
  have eq130710 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq130623 X0 X1
       have i₂ := eq62 X1
       grind)
    | exact superpose eq62 eq130623
    | (have j0 := eq130623 X0 X1
       grind)
    | exact resolve eq130623 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130623
  have eq132569 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (k y (τ (σ x))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq130461 y (σ x)
       have i₂ := eq42727
       grind)
    | exact superpose eq42727 eq130461
    | (have j0 := eq130461 y (σ x)
       grind)
    | exact resolve eq130461 eq42727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42727 eq130461
  have eq132592 : (M.op y y) = (k y (τ (σ x))) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq132569
       have r₂ := eq62 x
       grind)
    | exact resolve eq132569 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132569
  have eq132622 : (M.op y y) = (k y x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq132592
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq132592
    | exact resolve eq132592 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132592
  have eq132642 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (M.op y y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq132622
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq132622
    | exact resolve eq132622 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132622
  have eq132660 : (σ (k y x)) = (σ (M.op x x)) ∨ (M.op y y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq132642
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq132642
    | exact resolve eq132642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132642
  have eq132672 : (σ (k y x)) = (σ (M.op x x)) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq47354 y x
       grind)
    | (have r₁ := eq132660
       have r₂ := eq47354 y x
       grind)
    | exact resolve eq132660 eq47354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47354 eq132660
  have eq132970 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq35151 y x
       have i₂ := eq132672
       grind)
    | exact superpose eq132672 eq35151
    | (have j0 := eq35151 y x
       grind)
    | exact resolve eq35151 eq132672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35151 eq132672
  have eq133180 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) := by grind
  clear eq132970
  have eq133287 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq133180
       have r₂ := eq12 y x
       grind)
    | exact resolve eq133180 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133180
  have eq134152 : (M.op x y) = (τ (σ (M.op x x))) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq133287
       grind)
    | exact superpose eq133287 eq9
    | exact resolve eq9 eq133287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133287
  have eq134443 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq134152
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq134152
    | exact resolve eq134152 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134152
  have eq134445 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq134443
       have r₂ := eq12 y x
       grind)
    | exact resolve eq134443 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134443
  have eq135304 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq662 x y
       have i₂ := eq134445
       grind)
    | exact superpose eq134445 eq662
    | (have j0 := eq662 x y
       grind)
    | exact resolve eq662 eq134445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq135308 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16804 y x
       have i₂ := eq134445
       grind)
    | exact superpose eq134445 eq16804
    | (have j0 := eq16804 y x
       grind)
    | (have r₁ := eq16804 y x
       have r₂ := eq134445
       grind)
    | exact resolve eq16804 eq134445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134445
  have eq135392 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq135308
  have eq135393 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq135392
  have eq135397 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq135304
  have eq135402 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq635
       have i₂ := eq135393
       grind)
    | exact superpose eq135393 eq635
    | exact resolve eq635 eq135393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135403 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq135393
       grind)
    | exact superpose eq135393 eq11
    | (have j0 := eq11 y X0
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq135393
       grind)
    | exact resolve eq11 eq135393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135393
  have eq135483 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq135402
  have eq135495 : (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq135403 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135403
  have eq135514 : (M.op y y) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16804 y x
       have i₂ := eq135495
       grind)
    | exact superpose eq135495 eq16804
    | (have j0 := eq16804 y x
       grind)
    | exact resolve eq16804 eq135495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16804
  have eq135551 : (M.op y y) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq135514
  have eq140759 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq124726 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124726
  have eq142294 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq140759 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq140759
    | exact resolve eq140759 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140759
  have eq142419 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq142294 X0 X1
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq142294
    | (have j0 := eq142294 X0 X1
       grind)
    | exact resolve eq142294 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142294
  have eq142430 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq142419 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq142419
    | (have j0 := eq142419 X0 X1
       grind)
    | exact resolve eq142419 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142419
  have eq156925 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq130710 y x
       grind)
    | exact superpose eq130710 eq16
    | (have j1 := eq130710 y x
       grind)
    | exact resolve eq16 eq130710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130710
  have eq157276 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq156925
       have i₂ := eq45359 y x
       grind)
    | exact superpose eq45359 eq156925
    | (have j1 := eq45359 y x
       grind)
    | (have r₁ := eq156925
       have r₂ := eq45359 y x
       grind)
    | exact resolve eq156925 eq45359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45359 eq156925
  have eq157280 : (M.op y y) = (k y x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq157276
  have eq157287 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op y y) = (k y x) ∨ (k y x) = (M.op x x) := by
    first
    | (have j1 := eq142430 y x
       grind)
    | (have r₁ := eq157280
       have r₂ := eq142430 y x
       grind)
    | exact resolve eq157280 eq142430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157280
  have eq157292 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq42730
       have i₂ := eq157287
       grind)
    | exact superpose eq157287 eq42730
    | (have r₁ := eq42730
       have r₂ := eq157287
       grind)
    | exact resolve eq42730 eq157287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42730 eq157287
  have eq157512 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) := by grind
  clear eq157292
  have eq157513 : (k y x) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) = (k y x) := by grind
  clear eq157512
  have eq157611 : (k y x) = (M.op x x) ∨ (M.op y y) = (k y x) := by
    first
    | (have j1 := eq142430 y x
       grind)
    | (have r₁ := eq157513
       have r₂ := eq142430 y x
       grind)
    | exact resolve eq157513 eq142430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142430 eq157513
  have eq157641 : (M.op y y) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by grind
  clear eq157611
  have eq598159 : (σ (k y x)) = (τ (σ (σ (M.op y y)))) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9 (σ (k y x))
       have i₂ := eq130066
       grind)
    | exact superpose eq130066 eq9
    | exact resolve eq9 eq130066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130066
  have eq599120 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq598159
       have i₂ := eq9 (σ (M.op y y))
       grind)
    | exact superpose eq9 eq598159
    | exact resolve eq598159 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598159
  have eq599726 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq599120
  have eq2335015 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq71 y (σ x)
       have i₂ := eq135397
       grind)
    | exact superpose eq135397 eq71
    | (have j0 := eq71 y (σ x)
       grind)
    | (have r₁ := eq71 y (σ x)
       have r₂ := eq135397
       grind)
    | exact resolve eq71 eq135397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq135397
  have eq2335055 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq2335015
  have eq2335090 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2335055
       have i₂ := eq62 x
       grind)
    | exact superpose eq62 eq2335055
    | exact resolve eq2335055 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335055
  have eq2335158 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2335090
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2335090
    | exact resolve eq2335090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335090
  have eq2336634 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2335158
       have i₂ := eq26402 x y
       grind)
    | exact superpose eq26402 eq2335158
    | (have j1 := eq26402 x y
       grind)
    | exact resolve eq2335158 eq26402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26402 eq2335158
  have eq2336730 : (σ (k y x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2336634
  have eq2336753 : (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq2336730
       have r₂ := eq11 y x
       grind)
    | exact resolve eq2336730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336730
  have eq2336779 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have j1 := eq42298 x y
       grind)
    | (have r₁ := eq2336753
       have r₂ := eq42298 x y
       grind)
    | exact resolve eq2336753 eq42298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42298 eq2336753
  have eq2336815 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2336779
       grind)
    | exact superpose eq2336779 eq16
    | exact resolve eq16 eq2336779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336779
  have eq2337221 : (σ (k y x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq135483
  have eq2337389 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2337221
       have i₂ := eq135495
       grind)
    | exact superpose eq135495 eq2337221
    | exact resolve eq2337221 eq135495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337221
  have eq2337428 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2337389
  have eq2337429 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2337428
  have eq2337457 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq98 x (σ y)
       have i₂ := eq2337429
       grind)
    | exact superpose eq2337429 eq98
    | (have j0 := eq98 x (σ y)
       grind)
    | (have r₁ := eq98 x (σ y)
       have r₂ := eq2337429
       grind)
    | exact resolve eq98 eq2337429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq2337429
  have eq2337514 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2337457
  have eq2337553 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2337514
       have i₂ := eq62 y
       grind)
    | exact superpose eq62 eq2337514
    | exact resolve eq2337514 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337514
  have eq2337576 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2337553
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2337553
    | exact resolve eq2337553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337553
  have eq2337587 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2337576
       have i₂ := eq62 y
       grind)
    | exact superpose eq62 eq2337576
    | exact resolve eq2337576 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2337576
  have eq2337595 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2337587
       have r₂ := eq599726
       grind)
    | exact resolve eq2337587 eq599726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599726 eq2337587
  have eq2337703 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq2337595
       grind)
    | exact superpose eq2337595 eq9
    | exact resolve eq9 eq2337595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337595
  have eq2338988 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2337703
       have i₂ := eq9 (M.op y y)
       grind)
    | exact superpose eq9 eq2337703
    | exact resolve eq2337703 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337703
  have eq2339006 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq135495
       have i₂ := eq2338988
       grind)
    | exact superpose eq2338988 eq135495
    | exact resolve eq135495 eq2338988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135495 eq2338988
  have eq2339628 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2339006
  have eq2339680 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2339628
       have r₂ := eq135551
       grind)
    | exact resolve eq2339628 eq135551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135551 eq2339628
  have eq2339732 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq2336815
       have i₂ := eq2339680
       grind)
    | exact superpose eq2339680 eq2336815
    | exact resolve eq2336815 eq2339680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336815
  have eq2339733 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2339680
       grind)
    | exact superpose eq2339680 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2339680
       grind)
    | exact resolve eq12 eq2339680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2339741 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k y x) := by grind
  clear eq2339733
  have eq2339742 : (k y x) = (M.op x x) := by grind
  clear eq2339732
  have eq2339745 : (M.op y y) = (k y x) := by
    first
    | (have r₁ := eq2339741
       have r₂ := eq157641
       grind)
    | exact resolve eq2339741 eq157641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157641 eq2339741
  have eq2339853 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq2339745
       have i₂ := eq2339742
       grind)
    | exact superpose eq2339742 eq2339745
    | exact resolve eq2339745 eq2339742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339745
  have eq2339857 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq635
       have i₂ := eq2339853
       grind)
    | exact superpose eq2339853 eq635
    | exact resolve eq635 eq2339853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq2339853
  have eq2340328 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2339857
       have i₂ := eq2339680
       grind)
    | exact superpose eq2339680 eq2339857
    | exact resolve eq2339857 eq2339680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339857
  have eq2340329 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2340328
  have eq2340330 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2340329
       have i₂ := eq2339742
       grind)
    | exact superpose eq2339742 eq2340329
    | exact resolve eq2340329 eq2339742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339742 eq2340329
  have eq2340331 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2340330
  have eq2346570 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2340331
       grind)
    | exact superpose eq2340331 eq16
    | exact resolve eq16 eq2340331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340331
  have eq2346688 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2346570
       have i₂ := eq2339680
       grind)
    | exact superpose eq2339680 eq2346570
    | exact resolve eq2346570 eq2339680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339680 eq2346570
  have eq2346689 : False := by grind
  exact eq2346689
