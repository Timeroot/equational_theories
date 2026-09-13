import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else if m(X,Y) = X then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_x_pxx_x_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq20 (τ X0)
       grind)
    | exact superpose eq20 eq18
    | exact resolve eq18 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq30
    | exact resolve eq30 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq92 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq578 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) (τ X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq92
    | (have j0 := eq92 (τ X0) (τ X1)
       grind)
    | exact resolve eq92 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq592 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq585
    | (have j0 := eq585 X0 X1
       grind)
    | exact resolve eq585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq595 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq592
    | (have j0 := eq592 X0 X1
       grind)
    | exact resolve eq592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq597 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq595
    | (have j0 := eq595 X0 X1
       grind)
    | exact resolve eq595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq599 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq597
  have eq600 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq601 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq600
    | (have j0 := eq600 X0 X1
       grind)
    | exact resolve eq600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq602 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq601 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq601
    | (have j0 := eq601 X0 X1
       grind)
    | exact resolve eq601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq603 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq602
    | (have j0 := eq602 X0 X1
       grind)
    | exact resolve eq602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq4604 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq4645 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4604 X0 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq4604
    | (have j0 := eq4604 X0 X1
       grind)
    | exact resolve eq4604 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4604
  have eq5197 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq4645 X0 X1
       grind)
    | exact superpose eq4645 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq4645 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq4645 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq4645 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq4645 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq4645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5204 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4645 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645
  have eq5205 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5197
  have eq5206 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205
  have eq5214 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5206 X0 X1
       have j1 := eq5204 X0 X1
       grind)
    | (have r₁ := eq5206 (M.op X0 X0) X0
       have r₂ := eq5204 X0 X1
       grind)
    | (have r₁ := eq5206 X0 (M.op X0 X0)
       have r₂ := eq5204 X0 X1
       grind)
    | (have r₁ := eq5206 X0 X1
       have r₂ := eq5204 X0 X1
       grind)
    | exact resolve eq5206 eq5204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204 eq5206
  have eq5411 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq5214 X0 X1
       grind)
    | exact superpose eq5214 eq10
    | (have j1 := eq5214 X0 X1
       grind)
    | exact resolve eq10 eq5214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq5531 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5411 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5411
    | (have j0 := eq5411 X0 X1
       grind)
    | exact resolve eq5411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5411
  have eq5563 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq5531 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq5531 X1 X1
       grind)
    | exact superpose eq5531 eq11
    | (have j1 := eq5531 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5531 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq5531 X1 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5531 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq11 eq5531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5531
  have eq27819 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5563 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5563
  have eq27820 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27819 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27819
  have eq28058 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27820 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq27820
    | (have j0 := eq27820 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq27820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28142 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq27820 X0 (τ X1)
       grind)
    | exact superpose eq27820 eq19
    | (have j1 := eq27820 (k X0 (τ X1)) X0
       grind)
    | exact resolve eq19 eq27820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27820
  have eq29501 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (τ X0) = (τ X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq28142 (τ X0) X1
       grind)
    | exact superpose eq28142 eq18
    | (have j1 := eq28142 (τ X1) X0
       grind)
    | exact resolve eq18 eq28142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28142
  have eq29613 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ X0) = (τ X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29501 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq29501
    | (have j0 := eq29501 X0 X1
       grind)
    | exact resolve eq29501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29501
  have eq29689 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ X0) = (τ X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29613 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29613
    | (have j0 := eq29613 X0 X1
       grind)
    | exact resolve eq29613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29613
  have eq29741 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29689 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29689
    | (have j0 := eq29689 X0 X1
       grind)
    | exact resolve eq29689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29689
  have eq30289 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X1 (σ X0)) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29741 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29741
    | (have j0 := eq29741 X1 (σ X0)
       grind)
    | exact resolve eq29741 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29741
  have eq30651 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30289 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30289
    | (have j0 := eq30289 X1 (σ X0)
       grind)
    | exact resolve eq30289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30289
  have eq30957 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30651 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq30651
    | (have j0 := eq30651 X0 X1
       grind)
    | exact resolve eq30651 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30651
  have eq30981 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30957 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq30957
    | (have j0 := eq30957 X0 X1
       grind)
    | exact resolve eq30957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30957
  have eq32648 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30981 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50020 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28058 x y
       grind)
    | exact superpose eq28058 eq16
    | (have j1 := eq28058 x y
       grind)
    | exact resolve eq16 eq28058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28058
  have eq50409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq50020
       have i₂ := eq30981 x y
       grind)
    | exact superpose eq30981 eq50020
    | (have j1 := eq30981 x y
       grind)
    | (have r₁ := eq50020
       have r₂ := eq30981 x y
       grind)
    | (have r₁ := eq50020
       have r₂ := eq30981 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq50020
       have r₂ := eq30981 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq50020 eq30981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30981 eq50020
  have eq50416 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by grind
  clear eq50409
  have eq50420 : x = y ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq32648 x y
       grind)
    | (have r₁ := eq50416
       have r₂ := eq32648 x y
       grind)
    | exact resolve eq50416 eq32648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32648 eq50416
  have eq50421 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50420
       grind)
    | exact superpose eq50420 eq16
    | exact resolve eq16 eq50420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50420
  have eq50422 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq50421
       have r₂ := eq23 x
       grind)
    | exact resolve eq50421 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50421
  have eq50663 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq50422
       grind)
    | exact superpose eq50422 eq9
    | exact resolve eq9 eq50422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50422
  have eq50900 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq50663
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq50663
    | exact resolve eq50663 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50663
  have eq50902 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50900
       grind)
    | exact superpose eq50900 eq16
    | exact resolve eq16 eq50900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50900
  have eq50903 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq50902
       have r₂ := eq23 x
       grind)
    | exact resolve eq50902 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50902
  have eq51189 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92 x y
       have i₂ := eq50903
       grind)
    | exact superpose eq50903 eq92
    | (have j0 := eq92 x y
       grind)
    | (have r₁ := eq92 x y
       have r₂ := eq50903
       grind)
    | exact resolve eq92 eq50903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq51201 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq50903
       grind)
    | exact superpose eq50903 eq9
    | exact resolve eq9 eq50903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51370 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq51189
  have eq51442 : x = (k x y) := by
    first
    | (have i₁ := eq51201
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq51201
    | exact resolve eq51201 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51201
  have eq51456 : x ≠ x ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq603 x y
       have i₂ := eq51442
       grind)
    | exact superpose eq51442 eq603
    | (have j0 := eq603 x y
       grind)
    | (have r₁ := eq603 x y
       have r₂ := eq51442
       grind)
    | exact resolve eq603 eq51442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq51460 : x = y ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq51456
  have eq55261 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51460
       grind)
    | exact superpose eq51460 eq16
    | exact resolve eq16 eq51460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51460
  have eq55276 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq55261
       have r₂ := eq23 x
       grind)
    | exact resolve eq55261 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55261
  have eq55285 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  have eq109510 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46 x (σ y)
       have i₂ := eq51370
       grind)
    | exact superpose eq51370 eq46
    | (have j0 := eq46 x (σ y)
       grind)
    | (have r₁ := eq46 x (σ y)
       have r₂ := eq51370
       grind)
    | exact resolve eq46 eq51370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq109539 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq51370
  have eq109566 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq109510
  have eq109596 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109566
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq109566
    | exact resolve eq109566 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109566
  have eq109603 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109596
       have i₂ := eq50903
       grind)
    | exact superpose eq50903 eq109596
    | exact resolve eq109596 eq50903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50903 eq109596
  have eq109610 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq109603
       have r₂ := eq109539
       grind)
    | exact resolve eq109603 eq109539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109539 eq109603
  have eq110075 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109610
       grind)
    | exact superpose eq109610 eq16
    | exact resolve eq16 eq109610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109610
  have eq110148 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq110075
       have i₂ := eq55276
       grind)
    | exact superpose eq55276 eq110075
    | exact resolve eq110075 eq55276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55276
  have eq110166 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq110148
  have eq110647 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq110166
       grind)
    | exact superpose eq110166 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq110166
       grind)
    | exact resolve eq11 eq110166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110166
  have eq110655 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq110647
  have eq110659 : x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110655
       have i₂ := eq51442
       grind)
    | exact superpose eq51442 eq110655
    | exact resolve eq110655 eq51442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51442 eq110655
  have eq110664 : x ≠ x ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55285
       have i₂ := eq110659
       grind)
    | exact superpose eq110659 eq55285
    | (have r₁ := eq55285
       have r₂ := eq110659
       grind)
    | exact resolve eq55285 eq110659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55285 eq110659
  have eq110727 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq110664
  have eq111179 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110075
       have i₂ := eq110727
       grind)
    | exact superpose eq110727 eq110075
    | exact resolve eq110075 eq110727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110075 eq110727
  have eq111198 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq111179
  have eq111199 : (σ x) = (σ y) := by grind
  clear eq111198
  have eq111202 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111199
       grind)
    | exact superpose eq111199 eq16
    | exact resolve eq16 eq111199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111203 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq111199
       grind)
    | exact superpose eq111199 eq9
    | exact resolve eq9 eq111199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111199
  have eq111505 : x = y := by
    first
    | (have i₁ := eq111203
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq111203
    | exact resolve eq111203 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111203
  have eq111506 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq111202
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq111202
    | exact resolve eq111202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq111202
  have eq111507 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq111506
       have i₂ := eq111505
       grind)
    | exact superpose eq111505 eq111506
    | exact resolve eq111506 eq111505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111505 eq111506
  have eq111508 : False := by grind
  exact eq111508

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then Y else if m(X,Y) = X then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_x_pxx_y_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq20 (τ X0)
       grind)
    | exact superpose eq20 eq18
    | exact resolve eq18 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq30
    | exact resolve eq30 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq92 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq578 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) (τ X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq92
    | (have j0 := eq92 (τ X0) (τ X1)
       grind)
    | exact resolve eq92 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq592 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq585
    | (have j0 := eq585 X0 X1
       grind)
    | exact resolve eq585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq595 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq592
    | (have j0 := eq592 X0 X1
       grind)
    | exact resolve eq592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq597 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq595
    | (have j0 := eq595 X0 X1
       grind)
    | exact resolve eq595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq599 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq597
  have eq600 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq601 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq600
    | (have j0 := eq600 X0 X1
       grind)
    | exact resolve eq600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq602 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq601 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq601
    | (have j0 := eq601 X0 X1
       grind)
    | exact resolve eq601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq603 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq602
    | (have j0 := eq602 X0 X1
       grind)
    | exact resolve eq602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq4604 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq4645 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4604 X0 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq4604
    | (have j0 := eq4604 X0 X1
       grind)
    | exact resolve eq4604 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4604
  have eq5197 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq4645 X0 X1
       grind)
    | exact superpose eq4645 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq4645 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq4645 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq4645 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq4645 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq4645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5204 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4645 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645
  have eq5205 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5197
  have eq5206 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5205
  have eq5214 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5206 X0 X1
       have j1 := eq5204 X0 X1
       grind)
    | (have r₁ := eq5206 (M.op X0 X0) X0
       have r₂ := eq5204 X0 X1
       grind)
    | (have r₁ := eq5206 X0 (M.op X0 X0)
       have r₂ := eq5204 X0 X1
       grind)
    | (have r₁ := eq5206 X0 X1
       have r₂ := eq5204 X0 X1
       grind)
    | exact resolve eq5206 eq5204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204 eq5206
  have eq5411 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq5214 X0 X1
       grind)
    | exact superpose eq5214 eq10
    | (have j1 := eq5214 X0 X1
       grind)
    | exact resolve eq10 eq5214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5214
  have eq5531 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5411 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5411
    | (have j0 := eq5411 X0 X1
       grind)
    | exact resolve eq5411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5411
  have eq5563 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq5531 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq5531 X1 X1
       grind)
    | exact superpose eq5531 eq11
    | (have j1 := eq5531 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5531 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq5531 X1 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5531 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq11 eq5531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5531
  have eq27819 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5563 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5563
  have eq27820 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27819 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27819
  have eq28058 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27820 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq27820
    | (have j0 := eq27820 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq27820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28142 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq27820 X0 (τ X1)
       grind)
    | exact superpose eq27820 eq19
    | (have j1 := eq27820 (k X0 (τ X1)) X0
       grind)
    | exact resolve eq19 eq27820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq27820
  have eq29501 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (τ X0) = (τ X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq28142 (τ X0) X1
       grind)
    | exact superpose eq28142 eq18
    | (have j1 := eq28142 (τ X1) X0
       grind)
    | exact resolve eq18 eq28142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28142
  have eq29613 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ X0) = (τ X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29501 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq29501
    | (have j0 := eq29501 X0 X1
       grind)
    | exact resolve eq29501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29501
  have eq29689 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ X0) = (τ X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29613 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29613
    | (have j0 := eq29613 X0 X1
       grind)
    | exact resolve eq29613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29613
  have eq29741 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29689 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29689
    | (have j0 := eq29689 X0 X1
       grind)
    | exact resolve eq29689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29689
  have eq30289 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X1 (σ X0)) = X1 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29741 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq29741
    | (have j0 := eq29741 X1 (σ X0)
       grind)
    | exact resolve eq29741 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29741
  have eq30651 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30289 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30289
    | (have j0 := eq30289 X1 (σ X0)
       grind)
    | exact resolve eq30289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30289
  have eq30957 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30651 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq30651
    | (have j0 := eq30651 X0 X1
       grind)
    | exact resolve eq30651 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30651
  have eq30981 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30957 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq30957
    | (have j0 := eq30957 X0 X1
       grind)
    | exact resolve eq30957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30957
  have eq32648 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30981 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50020 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28058 x y
       grind)
    | exact superpose eq28058 eq16
    | (have j1 := eq28058 x y
       grind)
    | exact resolve eq16 eq28058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28058
  have eq50409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq50020
       have i₂ := eq30981 x y
       grind)
    | exact superpose eq30981 eq50020
    | (have j1 := eq30981 x y
       grind)
    | (have r₁ := eq50020
       have r₂ := eq30981 x y
       grind)
    | (have r₁ := eq50020
       have r₂ := eq30981 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq50020
       have r₂ := eq30981 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq50020 eq30981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30981 eq50020
  have eq50416 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (k x y)) ∨ x = y := by grind
  clear eq50409
  have eq50420 : x = y ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq32648 x y
       grind)
    | (have r₁ := eq50416
       have r₂ := eq32648 x y
       grind)
    | exact resolve eq50416 eq32648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32648 eq50416
  have eq50421 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50420
       grind)
    | exact superpose eq50420 eq16
    | exact resolve eq16 eq50420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50420
  have eq50422 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq50421
       have r₂ := eq23 x
       grind)
    | exact resolve eq50421 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50421
  have eq50663 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq50422
       grind)
    | exact superpose eq50422 eq9
    | exact resolve eq9 eq50422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50422
  have eq50900 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq50663
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq50663
    | exact resolve eq50663 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50663
  have eq50902 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50900
       grind)
    | exact superpose eq50900 eq16
    | exact resolve eq16 eq50900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50900
  have eq50903 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq50902
       have r₂ := eq23 x
       grind)
    | exact resolve eq50902 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50902
  have eq51189 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92 x y
       have i₂ := eq50903
       grind)
    | exact superpose eq50903 eq92
    | (have j0 := eq92 x y
       grind)
    | (have r₁ := eq92 x y
       have r₂ := eq50903
       grind)
    | exact resolve eq92 eq50903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq51201 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq50903
       grind)
    | exact superpose eq50903 eq9
    | exact resolve eq9 eq50903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51370 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq51189
  have eq51442 : x = (k x y) := by
    first
    | (have i₁ := eq51201
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq51201
    | exact resolve eq51201 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51201
  have eq51456 : x ≠ x ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq603 x y
       have i₂ := eq51442
       grind)
    | exact superpose eq51442 eq603
    | (have j0 := eq603 x y
       grind)
    | (have r₁ := eq603 x y
       have r₂ := eq51442
       grind)
    | exact resolve eq603 eq51442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq51460 : x = y ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq51456
  have eq55261 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51460
       grind)
    | exact superpose eq51460 eq16
    | exact resolve eq16 eq51460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51460
  have eq55276 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq55261
       have r₂ := eq23 x
       grind)
    | exact resolve eq55261 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55261
  have eq55285 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  have eq109510 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46 x (σ y)
       have i₂ := eq51370
       grind)
    | exact superpose eq51370 eq46
    | (have j0 := eq46 x (σ y)
       grind)
    | (have r₁ := eq46 x (σ y)
       have r₂ := eq51370
       grind)
    | exact resolve eq46 eq51370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq109539 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq51370
  have eq109566 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq109510
  have eq109596 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109566
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq109566
    | exact resolve eq109566 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109566
  have eq109603 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109596
       have i₂ := eq50903
       grind)
    | exact superpose eq50903 eq109596
    | exact resolve eq109596 eq50903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50903 eq109596
  have eq109610 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq109603
       have r₂ := eq109539
       grind)
    | exact resolve eq109603 eq109539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109539 eq109603
  have eq110075 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq109610
       grind)
    | exact superpose eq109610 eq16
    | exact resolve eq16 eq109610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109610
  have eq110148 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq110075
       have i₂ := eq55276
       grind)
    | exact superpose eq55276 eq110075
    | exact resolve eq110075 eq55276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55276
  have eq110166 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq110148
  have eq110647 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq110166
       grind)
    | exact superpose eq110166 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq110166
       grind)
    | exact resolve eq11 eq110166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110166
  have eq110655 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq110647
  have eq110659 : x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110655
       have i₂ := eq51442
       grind)
    | exact superpose eq51442 eq110655
    | exact resolve eq110655 eq51442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51442 eq110655
  have eq110664 : x ≠ x ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55285
       have i₂ := eq110659
       grind)
    | exact superpose eq110659 eq55285
    | (have r₁ := eq55285
       have r₂ := eq110659
       grind)
    | exact resolve eq55285 eq110659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55285 eq110659
  have eq110727 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq110664
  have eq111179 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq110075
       have i₂ := eq110727
       grind)
    | exact superpose eq110727 eq110075
    | exact resolve eq110075 eq110727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110075 eq110727
  have eq111198 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq111179
  have eq111199 : (σ x) = (σ y) := by grind
  clear eq111198
  have eq111202 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111199
       grind)
    | exact superpose eq111199 eq16
    | exact resolve eq16 eq111199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111203 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq111199
       grind)
    | exact superpose eq111199 eq9
    | exact resolve eq9 eq111199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111199
  have eq111505 : x = y := by
    first
    | (have i₁ := eq111203
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq111203
    | exact resolve eq111203 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111203
  have eq111506 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq111202
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq111202
    | exact resolve eq111202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq111202
  have eq111507 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq111506
       have i₂ := eq111505
       grind)
    | exact superpose eq111505 eq111506
    | exact resolve eq111506 eq111505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111505 eq111506
  have eq111508 : False := by grind
  exact eq111508

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if X = Y then X else if m(X,Y) = X then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_x_pxy_x_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
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
  have eq95 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
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
  have eq101 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq95 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq95 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq95 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq95
  have eq326 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq101 (σ X1) X0
       grind)
    | exact superpose eq101 eq15
    | (have j1 := eq101 (σ X1) X0
       grind)
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq551 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq326 X0 (σ X1)
       grind)
    | exact superpose eq326 eq29
    | (have j1 := eq326 X0 (σ X1)
       grind)
    | exact resolve eq29 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq552 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq326 X0 (τ X1)
       grind)
    | exact superpose eq326 eq19
    | (have j1 := eq326 X0 (τ X1)
       grind)
    | exact resolve eq19 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3354 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq5087 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq551 X0 X1
       grind)
    | exact superpose eq551 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq551 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq551 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq551 (M.op (σ X1) X1) X1
       grind)
    | exact resolve eq13 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5088 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (σ X1)
       have i₂ := eq551 X0 X1
       grind)
    | exact superpose eq551 eq11
    | (have j1 := eq551 X0 X1
       grind)
    | exact resolve eq11 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq5092 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5087 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087
  have eq5093 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5092 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5092
  have eq5100 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5093 X0 X1
       have j1 := eq5088 X0 X1
       grind)
    | (have r₁ := eq5093 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq5088 (σ X1) X1
       grind)
    | (have r₁ := eq5093 X0 X1
       have r₂ := eq5088 X0 X1
       grind)
    | exact resolve eq5093 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088 eq5093
  have eq5156 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq552
    | exact resolve eq552 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq5179 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5156 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5156
    | (have j0 := eq5156 X0 X1
       grind)
    | exact resolve eq5156 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156
  have eq5185 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq5179 X0 X1
       grind)
    | exact superpose eq5179 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq5179 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq5179 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq5179 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq5179 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq5179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5186 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq5179 X0 X1
       grind)
    | exact superpose eq5179 eq11
    | (have j1 := eq5179 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5179 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5179 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq5179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5179
  have eq5190 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5185
  have eq5191 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5190
  have eq5198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5191 X0 X1
       have j1 := eq5186 X0 X1
       grind)
    | (have r₁ := eq5191 (M.op X0 X0) X0
       have r₂ := eq5186 X0 X1
       grind)
    | (have r₁ := eq5191 X0 (M.op X0 X0)
       have r₂ := eq5186 X0 X1
       grind)
    | (have r₁ := eq5191 X0 X1
       have r₂ := eq5186 X0 X1
       grind)
    | exact resolve eq5191 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186 eq5191
  have eq6079 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq5100 (σ X0) X1
       grind)
    | exact superpose eq5100 eq38
    | (have j1 := eq5100 (σ X1) X0
       grind)
    | exact resolve eq38 eq5100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5100
  have eq6160 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6079 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq6079
    | (have j0 := eq6079 X0 X1
       grind)
    | exact resolve eq6079 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079
  have eq6193 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6160 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6160
    | (have j0 := eq6160 X0 X1
       grind)
    | exact resolve eq6160 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160
  have eq6203 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6193 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6193
    | (have j0 := eq6193 X0 X1
       grind)
    | exact resolve eq6193 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193
  have eq6726 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq6203 X0 X1
       grind)
    | exact superpose eq6203 eq10
    | (have j1 := eq6203 X0 X1
       grind)
    | exact resolve eq10 eq6203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203
  have eq8141 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6726 x y
       grind)
    | exact superpose eq6726 eq16
    | (have j1 := eq6726 x y
       grind)
    | exact resolve eq16 eq6726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6726
  have eq8263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8141
       have i₂ := eq326 x y
       grind)
    | exact superpose eq326 eq8141
    | (have j1 := eq326 x y
       grind)
    | (have r₁ := eq8141
       have r₂ := eq326 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8141
       have r₂ := eq326 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8141 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq8265 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq8141
       have i₂ := eq5198 x y
       grind)
    | exact superpose eq5198 eq8141
    | (have j1 := eq5198 x y
       grind)
    | (have r₁ := eq8141
       have r₂ := eq5198 x y
       grind)
    | (have r₁ := eq8141
       have r₂ := eq5198 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8141
       have r₂ := eq5198 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8141 eq5198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5198 eq8141
  have eq8266 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8265
  have eq8267 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq8266
  have eq8270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8263
  have eq8271 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8270
  have eq8274 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8267
       grind)
    | exact superpose eq8267 eq16
    | exact resolve eq16 eq8267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8267
  have eq8275 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8274
       have r₂ := eq23 x
       grind)
    | exact resolve eq8274 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8274
  have eq8417 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3354 x y
       have i₂ := eq8275
       grind)
    | exact superpose eq8275 eq3354
    | (have j0 := eq3354 x y
       grind)
    | exact resolve eq3354 eq8275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354 eq8275
  have eq8422 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8417
  have eq8423 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8422
  have eq8434 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8271
       grind)
    | exact superpose eq8271 eq16
    | exact resolve eq16 eq8271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8271
  have eq8435 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8434
       have r₂ := eq23 x
       grind)
    | exact resolve eq8434 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8434
  have eq8578 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8423
       grind)
    | exact superpose eq8423 eq16
    | exact resolve eq16 eq8423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8423
  have eq8685 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8578
       have i₂ := eq8435
       grind)
    | exact superpose eq8435 eq8578
    | exact resolve eq8578 eq8435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8435 eq8578
  have eq8690 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq8685
  have eq8691 : (σ x) = (σ y) := by grind
  clear eq8690
  have eq8692 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8691
       grind)
    | exact superpose eq8691 eq16
    | exact resolve eq16 eq8691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8693 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq8691
       grind)
    | exact superpose eq8691 eq9
    | exact resolve eq9 eq8691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8691
  have eq8772 : x = y := by
    first
    | (have i₁ := eq8693
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8693
    | exact resolve eq8693 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8693
  have eq8773 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8692
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq8692
    | exact resolve eq8692 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8692
  have eq8774 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8773
       have i₂ := eq8772
       grind)
    | exact superpose eq8772 eq8773
    | exact resolve eq8773 eq8772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8772 eq8773
  have eq8775 : False := by grind
  exact eq8775

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if X = Y then Y else if m(X,Y) = X then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_x_pxy_y_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
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
  have eq95 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
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
  have eq101 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq95 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq95 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq95 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq95
  have eq326 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq101 (σ X1) X0
       grind)
    | exact superpose eq101 eq15
    | (have j1 := eq101 (σ X1) X0
       grind)
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq551 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq326 X0 (σ X1)
       grind)
    | exact superpose eq326 eq29
    | (have j1 := eq326 X0 (σ X1)
       grind)
    | exact resolve eq29 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq552 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq326 X0 (τ X1)
       grind)
    | exact superpose eq326 eq19
    | (have j1 := eq326 X0 (τ X1)
       grind)
    | exact resolve eq19 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3354 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq5087 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq551 X0 X1
       grind)
    | exact superpose eq551 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq551 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq551 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq551 (M.op (σ X1) X1) X1
       grind)
    | exact resolve eq13 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5088 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (σ X1)
       have i₂ := eq551 X0 X1
       grind)
    | exact superpose eq551 eq11
    | (have j1 := eq551 X0 X1
       grind)
    | exact resolve eq11 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq5092 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5087 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087
  have eq5093 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5092 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5092
  have eq5100 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq5093 X0 X1
       have j1 := eq5088 X0 X1
       grind)
    | (have r₁ := eq5093 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq5088 (σ X1) X1
       grind)
    | (have r₁ := eq5093 X0 X1
       have r₂ := eq5088 X0 X1
       grind)
    | exact resolve eq5093 eq5088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088 eq5093
  have eq5156 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq552
    | exact resolve eq552 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq5179 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5156 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5156
    | (have j0 := eq5156 X0 X1
       grind)
    | exact resolve eq5156 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156
  have eq5185 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq5179 X0 X1
       grind)
    | exact superpose eq5179 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq5179 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq5179 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq5179 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq5179 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq5179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5186 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq5179 X0 X1
       grind)
    | exact superpose eq5179 eq11
    | (have j1 := eq5179 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5179 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5179 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq5179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5179
  have eq5190 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5185
  have eq5191 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5190
  have eq5198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5191 X0 X1
       have j1 := eq5186 X0 X1
       grind)
    | (have r₁ := eq5191 (M.op X0 X0) X0
       have r₂ := eq5186 X0 X1
       grind)
    | (have r₁ := eq5191 X0 (M.op X0 X0)
       have r₂ := eq5186 X0 X1
       grind)
    | (have r₁ := eq5191 X0 X1
       have r₂ := eq5186 X0 X1
       grind)
    | exact resolve eq5191 eq5186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186 eq5191
  have eq6079 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 (σ X1)
       have i₂ := eq5100 (σ X0) X1
       grind)
    | exact superpose eq5100 eq38
    | (have j1 := eq5100 (σ X1) X0
       grind)
    | exact resolve eq38 eq5100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5100
  have eq6160 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6079 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq6079
    | (have j0 := eq6079 X0 X1
       grind)
    | exact resolve eq6079 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079
  have eq6193 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6160 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6160
    | (have j0 := eq6160 X0 X1
       grind)
    | exact resolve eq6160 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160
  have eq6203 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6193 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6193
    | (have j0 := eq6193 X0 X1
       grind)
    | exact resolve eq6193 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193
  have eq6726 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq6203 X0 X1
       grind)
    | exact superpose eq6203 eq10
    | (have j1 := eq6203 X0 X1
       grind)
    | exact resolve eq10 eq6203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203
  have eq8141 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6726 x y
       grind)
    | exact superpose eq6726 eq16
    | (have j1 := eq6726 x y
       grind)
    | exact resolve eq16 eq6726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6726
  have eq8263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8141
       have i₂ := eq326 x y
       grind)
    | exact superpose eq326 eq8141
    | (have j1 := eq326 x y
       grind)
    | (have r₁ := eq8141
       have r₂ := eq326 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8141
       have r₂ := eq326 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8141 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq8265 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq8141
       have i₂ := eq5198 x y
       grind)
    | exact superpose eq5198 eq8141
    | (have j1 := eq5198 x y
       grind)
    | (have r₁ := eq8141
       have r₂ := eq5198 x y
       grind)
    | (have r₁ := eq8141
       have r₂ := eq5198 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8141
       have r₂ := eq5198 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8141 eq5198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5198 eq8141
  have eq8266 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8265
  have eq8267 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq8266
  have eq8270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8263
  have eq8271 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8270
  have eq8274 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8267
       grind)
    | exact superpose eq8267 eq16
    | exact resolve eq16 eq8267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8267
  have eq8275 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8274
       have r₂ := eq23 x
       grind)
    | exact resolve eq8274 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8274
  have eq8417 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3354 x y
       have i₂ := eq8275
       grind)
    | exact superpose eq8275 eq3354
    | (have j0 := eq3354 x y
       grind)
    | exact resolve eq3354 eq8275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354 eq8275
  have eq8422 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8417
  have eq8423 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8422
  have eq8434 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8271
       grind)
    | exact superpose eq8271 eq16
    | exact resolve eq16 eq8271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8271
  have eq8435 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8434
       have r₂ := eq23 x
       grind)
    | exact resolve eq8434 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8434
  have eq8578 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8423
       grind)
    | exact superpose eq8423 eq16
    | exact resolve eq16 eq8423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8423
  have eq8685 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8578
       have i₂ := eq8435
       grind)
    | exact superpose eq8435 eq8578
    | exact resolve eq8578 eq8435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8435 eq8578
  have eq8690 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq8685
  have eq8691 : (σ x) = (σ y) := by grind
  clear eq8690
  have eq8692 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8691
       grind)
    | exact superpose eq8691 eq16
    | exact resolve eq16 eq8691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8693 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq8691
       grind)
    | exact superpose eq8691 eq9
    | exact resolve eq9 eq8691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8691
  have eq8772 : x = y := by
    first
    | (have i₁ := eq8693
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8693
    | exact resolve eq8693 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8693
  have eq8773 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8692
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq8692
    | exact resolve eq8692 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8692
  have eq8774 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8773
       have i₂ := eq8772
       grind)
    | exact superpose eq8772 eq8773
    | exact resolve eq8773 eq8772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8772 eq8773
  have eq8775 : False := by grind
  exact eq8775

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else if m(X,Y) = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_y_pxx_x_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq20 (τ X0)
       grind)
    | exact superpose eq20 eq18
    | exact resolve eq18 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq30
    | exact resolve eq30 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq61 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq713 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) (τ X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq92
    | (have j0 := eq92 (τ X0) (τ X1)
       grind)
    | exact resolve eq92 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq713
    | (have j0 := eq713 X0 X1
       grind)
    | exact resolve eq713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq727 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq720
    | (have j0 := eq720 X0 X1
       grind)
    | exact resolve eq720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq730 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq727
    | (have j0 := eq727 X0 X1
       grind)
    | exact resolve eq727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq733 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq730 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq730
    | (have j0 := eq730 X0 X1
       grind)
    | exact resolve eq730 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq734 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq733
    | (have j0 := eq733 X0 X1
       grind)
    | exact resolve eq733 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq733
  have eq735 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq736 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq735
    | (have j0 := eq735 X0 X1
       grind)
    | exact resolve eq735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq737 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq736
    | (have j0 := eq736 X0 X1
       grind)
    | exact resolve eq736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq738 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq737 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq737
    | (have j0 := eq737 X0 X1
       grind)
    | exact resolve eq737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq4895 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq4936 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4895 X0 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq4895
    | (have j0 := eq4895 X0 X1
       grind)
    | exact resolve eq4895 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4895
  have eq5199 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq4936 X0 X1
       grind)
    | exact superpose eq4936 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq4936 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq4936 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq4936 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq4936 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5206 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4936 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936
  have eq5207 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199
  have eq5208 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq5216 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5208 X0 X1
       have j1 := eq5206 X1 X0
       grind)
    | (have r₁ := eq5208 (M.op X0 X0) X1
       have r₂ := eq5206 X0 (k X1 (M.op X0 X0))
       grind)
    | (have r₁ := eq5208 (M.op X0 X0) X1
       have r₂ := eq5206 X0 X1
       grind)
    | (have r₁ := eq5208 X1 (M.op X0 X0)
       have r₂ := eq5206 X0 X1
       grind)
    | exact resolve eq5208 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206 eq5208
  have eq5429 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq5216 X1 X0
       grind)
    | exact superpose eq5216 eq10
    | (have j1 := eq5216 X1 X0
       grind)
    | exact resolve eq10 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5549 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5429 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5429
    | (have j0 := eq5429 X0 X1
       grind)
    | exact resolve eq5429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429
  have eq5581 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq5549 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq5549 X1 X1
       grind)
    | exact superpose eq5549 eq11
    | (have j1 := eq5549 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5549 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq5549 X1 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5549 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq11 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5549
  have eq32874 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5581 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq32875 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32874 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32874
  have eq33266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32875 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq32875
    | (have j0 := eq32875 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq32875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33446 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq32875 (τ X0) X1
       grind)
    | exact superpose eq32875 eq18
    | (have j1 := eq32875 (τ X0) X1
       grind)
    | exact resolve eq18 eq32875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq32875
  have eq34873 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq33446 X1 (τ X0)
       grind)
    | exact superpose eq33446 eq19
    | (have j1 := eq33446 X0 (τ X1)
       grind)
    | exact resolve eq19 eq33446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq33446
  have eq34977 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34873 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq34873
    | (have j0 := eq34873 X0 X1
       grind)
    | exact resolve eq34873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34873
  have eq35067 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34977 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34977
    | (have j0 := eq34977 X0 X1
       grind)
    | exact resolve eq34977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34977
  have eq35128 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35067 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35067
    | (have j0 := eq35067 X0 X1
       grind)
    | exact resolve eq35067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35067
  have eq35740 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35128 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35128
    | (have j0 := eq35128 X1 (σ X0)
       grind)
    | exact resolve eq35128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35128
  have eq36196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35740 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35740
    | (have j0 := eq35740 X0 (σ X1)
       grind)
    | exact resolve eq35740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35740
  have eq36487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36196 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq36196
    | (have j0 := eq36196 X0 X1
       grind)
    | exact resolve eq36196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36196
  have eq36583 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36487 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq36487
    | (have j0 := eq36487 X0 X1
       grind)
    | exact resolve eq36487 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36487
  have eq37260 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq36583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56339 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33266 x y
       grind)
    | exact superpose eq33266 eq16
    | (have j1 := eq33266 x y
       grind)
    | exact resolve eq16 eq33266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33266
  have eq56764 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq56339
       have i₂ := eq36583 x y
       grind)
    | exact superpose eq36583 eq56339
    | (have j1 := eq36583 x y
       grind)
    | (have r₁ := eq56339
       have r₂ := eq36583 x y
       grind)
    | (have r₁ := eq56339
       have r₂ := eq36583 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq56339
       have r₂ := eq36583 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq56339 eq36583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36583 eq56339
  have eq56769 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (σ (k x y)) := by grind
  clear eq56764
  have eq56774 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have j1 := eq37260 x y
       grind)
    | (have r₁ := eq56769
       have r₂ := eq37260 x y
       grind)
    | exact resolve eq56769 eq37260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37260 eq56769
  have eq56775 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56774
       grind)
    | exact superpose eq56774 eq16
    | exact resolve eq16 eq56774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56774
  have eq56776 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq56775
       have r₂ := eq23 x
       grind)
    | exact resolve eq56775 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56775
  have eq57037 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq56776
       grind)
    | exact superpose eq56776 eq9
    | exact resolve eq9 eq56776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56776
  have eq57294 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq57037
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq57037
    | exact resolve eq57037 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57037
  have eq57296 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57294
       grind)
    | exact superpose eq57294 eq16
    | exact resolve eq16 eq57294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57294
  have eq57297 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq57296
       have r₂ := eq23 x
       grind)
    | exact resolve eq57296 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57296
  have eq57686 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92 x y
       have i₂ := eq57297
       grind)
    | exact superpose eq57297 eq92
    | (have j0 := eq92 x y
       grind)
    | (have r₁ := eq92 x y
       have r₂ := eq57297
       grind)
    | exact resolve eq92 eq57297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq57697 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq57297
       grind)
    | exact superpose eq57297 eq9
    | exact resolve eq9 eq57297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57888 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq57686
  have eq57960 : y = (k x y) := by
    first
    | (have i₁ := eq57697
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq57697
    | exact resolve eq57697 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57697
  have eq57974 : y ≠ y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq738 x y
       have i₂ := eq57960
       grind)
    | exact superpose eq57960 eq738
    | (have j0 := eq738 x y
       grind)
    | (have r₁ := eq738 x y
       have r₂ := eq57960
       grind)
    | exact resolve eq738 eq57960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq57979 : x = y ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq57974
  have eq61998 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57979
       grind)
    | exact superpose eq57979 eq16
    | exact resolve eq16 eq57979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57979
  have eq62013 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq61998
       have r₂ := eq23 x
       grind)
    | exact resolve eq61998 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61998
  have eq62023 : y ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  have eq137086 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46 x (σ y)
       have i₂ := eq57888
       grind)
    | exact superpose eq57888 eq46
    | (have j0 := eq46 x (σ y)
       grind)
    | (have r₁ := eq46 x (σ y)
       have r₂ := eq57888
       grind)
    | exact resolve eq46 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq137117 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq57888
  have eq137146 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq137086
  have eq137165 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq137146
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq137146
    | exact resolve eq137146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137146
  have eq137174 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq137165
       have i₂ := eq57297
       grind)
    | exact superpose eq57297 eq137165
    | exact resolve eq137165 eq57297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57297 eq137165
  have eq137180 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq137174
       have r₂ := eq137117
       grind)
    | exact resolve eq137174 eq137117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137117 eq137174
  have eq138128 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq137180
       grind)
    | exact superpose eq137180 eq16
    | exact resolve eq16 eq137180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137180
  have eq138215 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq138128
       have i₂ := eq62013
       grind)
    | exact superpose eq62013 eq138128
    | exact resolve eq138128 eq62013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62013
  have eq138235 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq138215
  have eq139410 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq138235
       grind)
    | exact superpose eq138235 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq138235
       grind)
    | exact resolve eq11 eq138235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138235
  have eq139418 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq139410
  have eq139421 : y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq139418
       have i₂ := eq57960
       grind)
    | exact superpose eq57960 eq139418
    | exact resolve eq139418 eq57960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57960 eq139418
  have eq139425 : y ≠ y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq62023
       have i₂ := eq139421
       grind)
    | exact superpose eq139421 eq62023
    | (have r₁ := eq62023
       have r₂ := eq139421
       grind)
    | exact resolve eq62023 eq139421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62023 eq139421
  have eq139469 : y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq139425
  have eq140384 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq138128
       have i₂ := eq139469
       grind)
    | exact superpose eq139469 eq138128
    | exact resolve eq138128 eq139469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138128 eq139469
  have eq140405 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq140384
  have eq140406 : (σ x) = (σ y) := by grind
  clear eq140405
  have eq140409 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140406
       grind)
    | exact superpose eq140406 eq16
    | exact resolve eq16 eq140406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140410 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq140406
       grind)
    | exact superpose eq140406 eq9
    | exact resolve eq9 eq140406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140406
  have eq140734 : x = y := by
    first
    | (have i₁ := eq140410
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq140410
    | exact resolve eq140410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140410
  have eq140735 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq140409
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq140409
    | exact resolve eq140409 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq140409
  have eq140736 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq140735
       have i₂ := eq140734
       grind)
    | exact superpose eq140734 eq140735
    | exact resolve eq140735 eq140734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140734 eq140735
  have eq140737 : False := by grind
  exact eq140737

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then Y else if m(X,Y) = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_y_pxx_y_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq20 (τ X0)
       grind)
    | exact superpose eq20 eq18
    | exact resolve eq18 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq30 X0
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq30
    | exact resolve eq30 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq11
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq61 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq713 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) (τ X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq92
    | (have j0 := eq92 (τ X0) (τ X1)
       grind)
    | exact resolve eq92 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq713
    | (have j0 := eq713 X0 X1
       grind)
    | exact resolve eq713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq727 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq720
    | (have j0 := eq720 X0 X1
       grind)
    | exact resolve eq720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq730 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq727
    | (have j0 := eq727 X0 X1
       grind)
    | exact resolve eq727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq733 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq730 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq730
    | (have j0 := eq730 X0 X1
       grind)
    | exact resolve eq730 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq734 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 X1
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq733
    | (have j0 := eq733 X0 X1
       grind)
    | exact resolve eq733 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq733
  have eq735 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq736 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq735
    | (have j0 := eq735 X0 X1
       grind)
    | exact resolve eq735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq737 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq736
    | (have j0 := eq736 X0 X1
       grind)
    | exact resolve eq736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq738 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq737 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq737
    | (have j0 := eq737 X0 X1
       grind)
    | exact resolve eq737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq4895 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq4936 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4895 X0 X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq4895
    | (have j0 := eq4895 X0 X1
       grind)
    | exact resolve eq4895 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4895
  have eq5199 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq4936 X0 X1
       grind)
    | exact superpose eq4936 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq4936 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq4936 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq4936 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq4936 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq4936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5206 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4936 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936
  have eq5207 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199
  have eq5208 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5207
  have eq5216 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq5208 X0 X1
       have j1 := eq5206 X1 X0
       grind)
    | (have r₁ := eq5208 (M.op X0 X0) X1
       have r₂ := eq5206 X0 (k X1 (M.op X0 X0))
       grind)
    | (have r₁ := eq5208 (M.op X0 X0) X1
       have r₂ := eq5206 X0 X1
       grind)
    | (have r₁ := eq5208 X1 (M.op X0 X0)
       have r₂ := eq5206 X0 X1
       grind)
    | exact resolve eq5208 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206 eq5208
  have eq5429 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq5216 X1 X0
       grind)
    | exact superpose eq5216 eq10
    | (have j1 := eq5216 X1 X0
       grind)
    | exact resolve eq10 eq5216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5549 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5429 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5429
    | (have j0 := eq5429 X0 X1
       grind)
    | exact resolve eq5429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5429
  have eq5581 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq5549 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq5549 X1 X1
       grind)
    | exact superpose eq5549 eq11
    | (have j1 := eq5549 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5549 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq5549 X1 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5549 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq11 eq5549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5549
  have eq32874 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5581 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq32875 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32874 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32874
  have eq33266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32875 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq32875
    | (have j0 := eq32875 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq32875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33446 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq32875 (τ X0) X1
       grind)
    | exact superpose eq32875 eq18
    | (have j1 := eq32875 (τ X0) X1
       grind)
    | exact resolve eq18 eq32875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq32875
  have eq34873 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq33446 X1 (τ X0)
       grind)
    | exact superpose eq33446 eq19
    | (have j1 := eq33446 X0 (τ X1)
       grind)
    | exact resolve eq19 eq33446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq33446
  have eq34977 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34873 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq34873
    | (have j0 := eq34873 X0 X1
       grind)
    | exact resolve eq34873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34873
  have eq35067 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34977 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34977
    | (have j0 := eq34977 X0 X1
       grind)
    | exact resolve eq34977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34977
  have eq35128 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35067 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35067
    | (have j0 := eq35067 X0 X1
       grind)
    | exact resolve eq35067 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35067
  have eq35740 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35128 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35128
    | (have j0 := eq35128 X1 (σ X0)
       grind)
    | exact resolve eq35128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35128
  have eq36196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35740 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35740
    | (have j0 := eq35740 X0 (σ X1)
       grind)
    | exact resolve eq35740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35740
  have eq36487 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36196 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq36196
    | (have j0 := eq36196 X0 X1
       grind)
    | exact resolve eq36196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36196
  have eq36583 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36487 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq36487
    | (have j0 := eq36487 X0 X1
       grind)
    | exact resolve eq36487 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36487
  have eq37260 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq36583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56339 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33266 x y
       grind)
    | exact superpose eq33266 eq16
    | (have j1 := eq33266 x y
       grind)
    | exact resolve eq16 eq33266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33266
  have eq56764 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq56339
       have i₂ := eq36583 x y
       grind)
    | exact superpose eq36583 eq56339
    | (have j1 := eq36583 x y
       grind)
    | (have r₁ := eq56339
       have r₂ := eq36583 x y
       grind)
    | (have r₁ := eq56339
       have r₂ := eq36583 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq56339
       have r₂ := eq36583 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq56339 eq36583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36583 eq56339
  have eq56769 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (σ (k x y)) := by grind
  clear eq56764
  have eq56774 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have j1 := eq37260 x y
       grind)
    | (have r₁ := eq56769
       have r₂ := eq37260 x y
       grind)
    | exact resolve eq56769 eq37260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37260 eq56769
  have eq56775 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56774
       grind)
    | exact superpose eq56774 eq16
    | exact resolve eq16 eq56774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56774
  have eq56776 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq56775
       have r₂ := eq23 x
       grind)
    | exact resolve eq56775 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56775
  have eq57037 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq56776
       grind)
    | exact superpose eq56776 eq9
    | exact resolve eq9 eq56776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56776
  have eq57294 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq57037
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq57037
    | exact resolve eq57037 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57037
  have eq57296 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57294
       grind)
    | exact superpose eq57294 eq16
    | exact resolve eq16 eq57294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57294
  have eq57297 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq57296
       have r₂ := eq23 x
       grind)
    | exact resolve eq57296 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57296
  have eq57686 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92 x y
       have i₂ := eq57297
       grind)
    | exact superpose eq57297 eq92
    | (have j0 := eq92 x y
       grind)
    | (have r₁ := eq92 x y
       have r₂ := eq57297
       grind)
    | exact resolve eq92 eq57297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq57697 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq57297
       grind)
    | exact superpose eq57297 eq9
    | exact resolve eq9 eq57297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57888 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq57686
  have eq57960 : y = (k x y) := by
    first
    | (have i₁ := eq57697
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq57697
    | exact resolve eq57697 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57697
  have eq57974 : y ≠ y ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq738 x y
       have i₂ := eq57960
       grind)
    | exact superpose eq57960 eq738
    | (have j0 := eq738 x y
       grind)
    | (have r₁ := eq738 x y
       have r₂ := eq57960
       grind)
    | exact resolve eq738 eq57960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq57979 : x = y ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq57974
  have eq61998 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57979
       grind)
    | exact superpose eq57979 eq16
    | exact resolve eq16 eq57979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57979
  have eq62013 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq61998
       have r₂ := eq23 x
       grind)
    | exact resolve eq61998 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61998
  have eq62023 : y ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  have eq137086 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46 x (σ y)
       have i₂ := eq57888
       grind)
    | exact superpose eq57888 eq46
    | (have j0 := eq46 x (σ y)
       grind)
    | (have r₁ := eq46 x (σ y)
       have r₂ := eq57888
       grind)
    | exact resolve eq46 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq137117 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq57888
  have eq137146 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq137086
  have eq137165 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq137146
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq137146
    | exact resolve eq137146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137146
  have eq137174 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq137165
       have i₂ := eq57297
       grind)
    | exact superpose eq57297 eq137165
    | exact resolve eq137165 eq57297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57297 eq137165
  have eq137180 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq137174
       have r₂ := eq137117
       grind)
    | exact resolve eq137174 eq137117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137117 eq137174
  have eq138128 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq137180
       grind)
    | exact superpose eq137180 eq16
    | exact resolve eq16 eq137180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137180
  have eq138215 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq138128
       have i₂ := eq62013
       grind)
    | exact superpose eq62013 eq138128
    | exact resolve eq138128 eq62013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62013
  have eq138235 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq138215
  have eq139410 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq138235
       grind)
    | exact superpose eq138235 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq138235
       grind)
    | exact resolve eq11 eq138235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138235
  have eq139418 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq139410
  have eq139421 : y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq139418
       have i₂ := eq57960
       grind)
    | exact superpose eq57960 eq139418
    | exact resolve eq139418 eq57960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57960 eq139418
  have eq139425 : y ≠ y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq62023
       have i₂ := eq139421
       grind)
    | exact superpose eq139421 eq62023
    | (have r₁ := eq62023
       have r₂ := eq139421
       grind)
    | exact resolve eq62023 eq139421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62023 eq139421
  have eq139469 : y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq139425
  have eq140384 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq138128
       have i₂ := eq139469
       grind)
    | exact superpose eq139469 eq138128
    | exact resolve eq138128 eq139469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138128 eq139469
  have eq140405 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq140384
  have eq140406 : (σ x) = (σ y) := by grind
  clear eq140405
  have eq140409 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq140406
       grind)
    | exact superpose eq140406 eq16
    | exact resolve eq16 eq140406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140410 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq140406
       grind)
    | exact superpose eq140406 eq9
    | exact resolve eq9 eq140406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140406
  have eq140734 : x = y := by
    first
    | (have i₁ := eq140410
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq140410
    | exact resolve eq140410 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140410
  have eq140735 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq140409
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq140409
    | exact resolve eq140409 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq140409
  have eq140736 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq140735
       have i₂ := eq140734
       grind)
    | exact superpose eq140734 eq140735
    | exact resolve eq140735 eq140734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140734 eq140735
  have eq140737 : False := by grind
  exact eq140737

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if X = Y then X else if m(X,Y) = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_y_pxy_x_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
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
  have eq95 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
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
  clear eq19 eq84
  have eq101 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq95 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq95 (σ (M.op X0 X0)) X0
       have r₂ := eq46 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq95 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq95 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq95
  have eq326 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq101 (σ X1) X0
       grind)
    | exact superpose eq101 eq15
    | (have j1 := eq101 (σ X1) X0
       grind)
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq563 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq326 (τ X0) X1
       grind)
    | exact superpose eq326 eq18
    | (have j1 := eq326 (τ X0) X1
       grind)
    | exact resolve eq18 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3672 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq5121 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq563 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq563
    | exact resolve eq563 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq5143 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5121 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5121
    | (have j0 := eq5121 X0 X1
       grind)
    | exact resolve eq5121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5121
  have eq5211 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq5143 X0 X1
       grind)
    | exact superpose eq5143 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq5143 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq5143 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq5143 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq5143 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq5143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5212 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq5143 X0 X1
       grind)
    | exact superpose eq5143 eq11
    | (have j1 := eq5143 X1 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq5143 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5143 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5143 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq5143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5143
  have eq5216 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211
  have eq5217 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5217 X0 X1
       have j1 := eq5212 X0 X1
       grind)
    | (have r₁ := eq5217 (M.op X1 X1) X1
       have r₂ := eq5212 (k X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq5217 (M.op X1 X1) X0
       have r₂ := eq5212 X0 X1
       grind)
    | (have r₁ := eq5217 X0 (M.op X1 X1)
       have r₂ := eq5212 X0 X1
       grind)
    | exact resolve eq5217 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212 eq5217
  have eq5276 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq5224 X1 X0
       grind)
    | exact superpose eq5224 eq9
    | (have j1 := eq5224 (k X0 X1) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq9 eq5224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5331 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5276 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq5276
    | (have j0 := eq5276 X0 X1
       grind)
    | exact resolve eq5276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276
  have eq5434 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq5331 (σ X0) X1
       grind)
    | exact superpose eq5331 eq38
    | (have j1 := eq5331 (σ X0) X1
       grind)
    | exact resolve eq38 eq5331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5331
  have eq6233 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) X0
       have i₂ := eq5434 X1 (σ X0)
       grind)
    | exact superpose eq5434 eq29
    | (have j1 := eq5434 X0 (σ X1)
       grind)
    | exact resolve eq29 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5434
  have eq6316 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6233 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq6233
    | (have j0 := eq6233 X0 X1
       grind)
    | exact resolve eq6233 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6233
  have eq6354 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6316 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6316
    | (have j0 := eq6316 X0 X1
       grind)
    | exact resolve eq6316 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6316
  have eq6365 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6354 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6354
    | (have j0 := eq6354 X0 X1
       grind)
    | exact resolve eq6354 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6354
  have eq6625 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq6365 X1 X0
       grind)
    | exact superpose eq6365 eq10
    | (have j1 := eq6365 X1 X0
       grind)
    | exact resolve eq10 eq6365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6365
  have eq8133 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6625 x y
       grind)
    | exact superpose eq6625 eq16
    | (have j1 := eq6625 x y
       grind)
    | exact resolve eq16 eq6625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6625
  have eq8194 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8133
       have i₂ := eq326 x y
       grind)
    | exact superpose eq326 eq8133
    | (have j1 := eq326 x y
       grind)
    | (have r₁ := eq8133
       have r₂ := eq326 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8133
       have r₂ := eq326 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8133 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq8196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq8133
       have i₂ := eq5224 y x
       grind)
    | exact superpose eq5224 eq8133
    | (have j1 := eq5224 y (k x y)
       grind)
    | (have r₁ := eq8133
       have r₂ := eq5224 y x
       grind)
    | (have r₁ := eq8133
       have r₂ := eq5224 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8133
       have r₂ := eq5224 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8133 eq5224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5224 eq8133
  have eq8197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8196
  have eq8198 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq8197
  have eq8201 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8194
  have eq8202 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq8201
  have eq8268 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8198
       grind)
    | exact superpose eq8198 eq16
    | exact resolve eq16 eq8198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8269 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8268
       have r₂ := eq23 x
       grind)
    | exact resolve eq8268 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8268
  have eq8280 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3672 x y
       have i₂ := eq8269
       grind)
    | exact superpose eq8269 eq3672
    | (have j0 := eq3672 x y
       grind)
    | exact resolve eq3672 eq8269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672 eq8269
  have eq8285 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8280
  have eq8286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8285
  have eq8381 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8202
       grind)
    | exact superpose eq8202 eq16
    | exact resolve eq16 eq8202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8202
  have eq8382 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8381
       have r₂ := eq23 x
       grind)
    | exact resolve eq8381 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8381
  have eq8477 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8286
       grind)
    | exact superpose eq8286 eq16
    | exact resolve eq16 eq8286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8286
  have eq8505 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8477
       have i₂ := eq8382
       grind)
    | exact superpose eq8382 eq8477
    | exact resolve eq8477 eq8382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8382 eq8477
  have eq8510 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq8505
  have eq8511 : (σ x) = (σ y) := by grind
  clear eq8510
  have eq8592 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8511
       grind)
    | exact superpose eq8511 eq16
    | exact resolve eq16 eq8511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8593 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq8511
       grind)
    | exact superpose eq8511 eq9
    | exact resolve eq9 eq8511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8511
  have eq8669 : x = y := by
    first
    | (have i₁ := eq8593
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8593
    | exact resolve eq8593 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8593
  have eq8670 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8592
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq8592
    | exact resolve eq8592 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8592
  have eq8671 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8670
       have i₂ := eq8669
       grind)
    | exact superpose eq8669 eq8670
    | exact resolve eq8670 eq8669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8669 eq8670
  have eq8672 : False := by grind
  exact eq8672

/-- `x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if X = Y then Y else if m(X,Y) = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_y_pxy_y_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq46 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
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
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
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
  have eq95 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
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
  clear eq19 eq84
  have eq101 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq46 X1 X0
       grind)
    | (have r₁ := eq95 X1 X0
       have r₂ := eq46 X0 X1
       grind)
    | (have r₁ := eq95 (σ (M.op X0 X0)) X0
       have r₂ := eq46 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq95 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq46 X0 X1
       grind)
    | exact resolve eq95 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq95
  have eq326 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101
    | exact resolve eq101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq101 (σ X1) X0
       grind)
    | exact superpose eq101 eq15
    | (have j1 := eq101 (σ X1) X0
       grind)
    | exact resolve eq15 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq563 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq326 (τ X0) X1
       grind)
    | exact superpose eq326 eq18
    | (have j1 := eq326 (τ X0) X1
       grind)
    | exact resolve eq18 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3672 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq5121 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq563 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq563
    | exact resolve eq563 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq5143 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5121 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5121
    | (have j0 := eq5121 X0 X1
       grind)
    | exact resolve eq5121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5121
  have eq5211 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq5143 X0 X1
       grind)
    | exact superpose eq5143 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq5143 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq5143 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq5143 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq5143 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq5143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5212 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq5143 X0 X1
       grind)
    | exact superpose eq5143 eq11
    | (have j1 := eq5143 X1 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq5143 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5143 (M.op X0 X0) (M.op X0 X1)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq5143 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq11 eq5143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5143
  have eq5216 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211
  have eq5217 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5217 X0 X1
       have j1 := eq5212 X0 X1
       grind)
    | (have r₁ := eq5217 (M.op X1 X1) X1
       have r₂ := eq5212 (k X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq5217 (M.op X1 X1) X0
       have r₂ := eq5212 X0 X1
       grind)
    | (have r₁ := eq5217 X0 (M.op X1 X1)
       have r₂ := eq5212 X0 X1
       grind)
    | exact resolve eq5217 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212 eq5217
  have eq5276 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq5224 X1 X0
       grind)
    | exact superpose eq5224 eq9
    | (have j1 := eq5224 (k X0 X1) (τ (σ (M.op X0 X1)))
       grind)
    | exact resolve eq9 eq5224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5331 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5276 X0 X1
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq5276
    | (have j0 := eq5276 X0 X1
       grind)
    | exact resolve eq5276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276
  have eq5434 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq5331 (σ X0) X1
       grind)
    | exact superpose eq5331 eq38
    | (have j1 := eq5331 (σ X0) X1
       grind)
    | exact resolve eq38 eq5331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5331
  have eq6233 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) X0
       have i₂ := eq5434 X1 (σ X0)
       grind)
    | exact superpose eq5434 eq29
    | (have j1 := eq5434 X0 (σ X1)
       grind)
    | exact resolve eq29 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5434
  have eq6316 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6233 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq6233
    | (have j0 := eq6233 X0 X1
       grind)
    | exact resolve eq6233 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6233
  have eq6354 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6316 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6316
    | (have j0 := eq6316 X0 X1
       grind)
    | exact resolve eq6316 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6316
  have eq6365 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6354 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6354
    | (have j0 := eq6354 X0 X1
       grind)
    | exact resolve eq6354 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6354
  have eq6625 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X1))
       have i₂ := eq6365 X1 X0
       grind)
    | exact superpose eq6365 eq10
    | (have j1 := eq6365 X1 X0
       grind)
    | exact resolve eq10 eq6365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6365
  have eq8133 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6625 x y
       grind)
    | exact superpose eq6625 eq16
    | (have j1 := eq6625 x y
       grind)
    | exact resolve eq16 eq6625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6625
  have eq8194 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8133
       have i₂ := eq326 x y
       grind)
    | exact superpose eq326 eq8133
    | (have j1 := eq326 x y
       grind)
    | (have r₁ := eq8133
       have r₂ := eq326 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8133
       have r₂ := eq326 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8133 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq8196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq8133
       have i₂ := eq5224 y x
       grind)
    | exact superpose eq5224 eq8133
    | (have j1 := eq5224 y (k x y)
       grind)
    | (have r₁ := eq8133
       have r₂ := eq5224 y x
       grind)
    | (have r₁ := eq8133
       have r₂ := eq5224 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq8133
       have r₂ := eq5224 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8133 eq5224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5224 eq8133
  have eq8197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8196
  have eq8198 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq8197
  have eq8201 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8194
  have eq8202 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq8201
  have eq8268 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8198
       grind)
    | exact superpose eq8198 eq16
    | exact resolve eq16 eq8198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8269 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8268
       have r₂ := eq23 x
       grind)
    | exact resolve eq8268 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8268
  have eq8280 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3672 x y
       have i₂ := eq8269
       grind)
    | exact superpose eq8269 eq3672
    | (have j0 := eq3672 x y
       grind)
    | exact resolve eq3672 eq8269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672 eq8269
  have eq8285 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8280
  have eq8286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8285
  have eq8381 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8202
       grind)
    | exact superpose eq8202 eq16
    | exact resolve eq16 eq8202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8202
  have eq8382 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8381
       have r₂ := eq23 x
       grind)
    | exact resolve eq8381 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8381
  have eq8477 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8286
       grind)
    | exact superpose eq8286 eq16
    | exact resolve eq16 eq8286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8286
  have eq8505 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8477
       have i₂ := eq8382
       grind)
    | exact superpose eq8382 eq8477
    | exact resolve eq8477 eq8382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8382 eq8477
  have eq8510 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq8505
  have eq8511 : (σ x) = (σ y) := by grind
  clear eq8510
  have eq8592 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8511
       grind)
    | exact superpose eq8511 eq16
    | exact resolve eq16 eq8511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8593 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq8511
       grind)
    | exact superpose eq8511 eq9
    | exact resolve eq9 eq8511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8511
  have eq8669 : x = y := by
    first
    | (have i₁ := eq8593
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8593
    | exact resolve eq8593 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8593
  have eq8670 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8592
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq8592
    | exact resolve eq8592 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8592
  have eq8671 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8670
       have i₂ := eq8669
       grind)
    | exact superpose eq8669 eq8670
    | exact resolve eq8670 eq8669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8669 eq8670
  have eq8672 : False := by grind
  exact eq8672
