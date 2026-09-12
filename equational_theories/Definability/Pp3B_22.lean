import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq62 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq474 (σ X0)
       grind)
    | exact superpose eq474 eq15
    | (have j1 := eq474 (σ X0)
       grind)
    | exact resolve eq15 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq529 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq485
  have eq531 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq529 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq529
    | (have j0 := eq529 X0
       grind)
    | exact resolve eq529 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq532 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq541 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq532 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq532
    | exact resolve eq532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0) (σ X0)
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq62
    | exact resolve eq62 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq541 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq541
    | exact resolve eq541 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq541
  have eq574 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq571 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq571
    | exact resolve eq571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq591 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq574 (τ X0)
       grind)
    | exact superpose eq574 eq32
    | exact resolve eq32 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq591 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq591
    | exact resolve eq591 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq670 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq553 (k X0 X0) (M.op x (σ X0))
       have i₂ := eq553 X0 x
       grind)
    | exact superpose eq553 eq553
    | exact resolve eq553 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq798 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (M.op (k X0 X0) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq768 X0
       have i₂ := eq574 (k X0 X0)
       grind)
    | exact superpose eq574 eq768
    | exact resolve eq768 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq810 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq798 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq798
    | exact resolve eq798 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq818 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq810 X0
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq810 X0
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq810
    | exact resolve eq810 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq810
  have eq837 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq818
  have eq854 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq837 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq837
    | exact resolve eq837 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq862 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq854
  have eq42942 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq670 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq670
    | exact resolve eq670 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq43251 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq42942 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq42942
    | (have j0 := eq42942 X0 X1
       grind)
    | exact resolve eq42942 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42942
  have eq43469 : ∀ X0 X1 : G, (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X0 X1))) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43251 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq43251
    | (have j0 := eq43251 (τ X0) (τ X1)
       grind)
    | exact resolve eq43251 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43251
  have eq43704 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op (τ X1) (τ X0))) = (τ (τ (k X0 X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43469 X0 X1
       have i₂ := eq598 X1
       grind)
    | exact superpose eq598 eq43469
    | (have j0 := eq43469 X0 X1
       grind)
    | exact resolve eq43469 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43469
  have eq782834 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq43704 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq43704 X0 X1
       grind)
    | exact superpose eq43704 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq43704 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq43704 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq43704 X0 X1
       grind)
    | exact resolve eq13 eq43704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43704
  have eq782876 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq782834 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782834
  have eq782883 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq782876 X0 X1
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq782876
    | (have j0 := eq782876 X0 X1
       grind)
    | exact resolve eq782876 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq782876
  have eq782884 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq782883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782883
  have eq783084 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (τ (M.op X0 X0)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq782884 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq782884
    | (have j0 := eq782884 X0 X1
       grind)
    | exact resolve eq782884 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782884
  have eq783887 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq783084 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq783084
    | exact resolve eq783084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783084
  have eq784913 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (M.op X1 X1)) = X0 ∨ (τ (τ (k (σ X0) X1))) = (τ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq783887 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq783887
    | (have j0 := eq783887 X0 X1
       grind)
    | exact resolve eq783887 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783887
  have eq785320 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (k X0 (τ X1))) = (τ (M.op (τ X1) X0)) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq784913 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq784913
    | (have j0 := eq784913 X0 X1
       grind)
    | exact resolve eq784913 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784913
  have eq786916 : ∀ X0 X1 : G, (k X1 (τ (τ X0))) = (τ (M.op (τ X0) (σ X1))) ∨ (τ (k (σ X1) (τ X0))) = (τ (M.op (τ X0) (σ X1))) ∨ (σ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq785320 (σ X1) X0
       grind)
    | exact superpose eq785320 eq29
    | (have j1 := eq785320 (σ X1) X0
       grind)
    | exact resolve eq29 eq785320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785320
  have eq787980 : ∀ X0 X1 : G, (k X1 (τ (τ X0))) = (τ (M.op (τ X0) (σ X1))) ∨ (k X1 (τ (τ X0))) = (τ (M.op (τ X0) (σ X1))) ∨ (σ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq786916 X0 X1
       have i₂ := eq29 X1 (τ X0)
       grind)
    | exact superpose eq29 eq786916
    | (have j0 := eq786916 X0 X1
       grind)
    | exact resolve eq786916 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq786916
  have eq787981 : ∀ X0 X1 : G, (k X1 (τ (τ X0))) = (τ (M.op (τ X0) (σ X1))) ∨ (σ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq787980 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787980
  have eq788794 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq787981 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq787981
    | (have j0 := eq787981 (σ X0) X1
       grind)
    | exact resolve eq787981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787981
  have eq790160 : ∀ X0 X1 : G, (σ X1) = (τ (σ (k X0 X0))) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq788794 X0 X1
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq788794
    | (have j0 := eq788794 X0 X1
       grind)
    | exact resolve eq788794 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788794
  have eq790253 : ∀ X0 X1 : G, (σ X1) = (k X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq790160 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq790160
    | (have j0 := eq790160 X0 X1
       grind)
    | exact resolve eq790160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790160
  have eq790316 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq790253 X0 X1
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq790253
    | (have j0 := eq790253 X0 X1
       grind)
    | exact resolve eq790253 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790253
  have eq790540 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq790316 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq790316
    | exact resolve eq790316 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790316
  have eq792255 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq790540 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq790540
    | (have j0 := eq790540 X0 X1
       grind)
    | exact resolve eq790540 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq790540
  have eq793538 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq792255 X1 X0
       grind)
    | exact superpose eq792255 eq11
    | (have j1 := eq792255 X1 X0
       grind)
    | exact resolve eq11 eq792255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792255
  have eq795448 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq793538 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq793538
    | (have j0 := eq793538 X0 X1
       grind)
    | exact resolve eq793538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793538
  have eq796799 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq795448 (σ X0) (σ X1)
       grind)
    | exact superpose eq795448 eq15
    | (have j1 := eq795448 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq795448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796821 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq795448 X0 (τ X1)
       grind)
    | exact superpose eq795448 eq18
    | (have j1 := eq795448 X0 (τ X1)
       grind)
    | exact resolve eq18 eq795448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq795448
  have eq798183 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq796799 X0 X1
       have i₂ := eq532 X0
       grind)
    | exact superpose eq532 eq796799
    | (have j0 := eq796799 X0 X1
       grind)
    | exact resolve eq796799 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq796799
  have eq798746 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq798183 X0 X1
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq798183
    | (have j0 := eq798183 X0 X1
       grind)
    | exact resolve eq798183 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq798183
  have eq805013 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq796821 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq796821
    | exact resolve eq796821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796821
  have eq805787 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq805013 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq805013
    | (have j0 := eq805013 X0 X1
       grind)
    | exact resolve eq805013 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805013
  have eq820287 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq798746 x y
       grind)
    | exact superpose eq798746 eq16
    | (have j1 := eq798746 x y
       grind)
    | exact resolve eq16 eq798746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798746
  have eq822966 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq820287
       have i₂ := eq805787 y x
       grind)
    | exact superpose eq805787 eq820287
    | (have j1 := eq805787 y x
       grind)
    | (have r₁ := eq820287
       have r₂ := eq805787 y x
       grind)
    | exact resolve eq820287 eq805787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805787 eq820287
  have eq822969 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq822966
  have eq822988 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq862 x
       have i₂ := eq822969
       grind)
    | exact superpose eq822969 eq862
    | exact resolve eq862 eq822969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822969
  have eq823284 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq822988
       have r₂ := eq16
       grind)
    | exact resolve eq822988 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822988
  have eq823360 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq823284
       grind)
    | exact superpose eq823284 eq10
    | exact resolve eq10 eq823284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823284
  have eq823840 : y = (M.op x x) := by
    first
    | (have i₁ := eq823360
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq823360
    | exact resolve eq823360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823360
  have eq823965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq862 x
       have i₂ := eq823840
       grind)
    | exact superpose eq823840 eq862
    | exact resolve eq862 eq823840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq823840
  have eq824261 : False := by grind
  exact eq824261

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33
    | exact resolve eq33 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq83 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq42
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq172 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq673 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq186 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq186
    | (have j0 := eq186 (τ X1) (τ X0)
       grind)
    | exact resolve eq186 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq673 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq673
    | (have j0 := eq673 X0 X1
       grind)
    | exact resolve eq673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq684 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq686 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq684
    | (have j0 := eq684 X0 X1
       grind)
    | exact resolve eq684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq687 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq686
    | (have j0 := eq686 X0 X1
       grind)
    | exact resolve eq686 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq688 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq687 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq687
    | (have j0 := eq687 X0 X1
       grind)
    | exact resolve eq687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq689 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq3635 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 (σ X1) X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3661 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq83 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq3662 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3665 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3635 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3635
  have eq3666 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3665 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3665
  have eq3668 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3662 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3662
    | (have j0 := eq3662 X0
       grind)
    | exact resolve eq3662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq3708 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq3668 X0
       grind)
    | exact superpose eq3668 eq49
    | (have j1 := eq3668 X0
       grind)
    | exact resolve eq49 eq3668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3668
  have eq3732 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3708 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3708
    | (have j0 := eq3708 X0
       grind)
    | exact resolve eq3708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3708
  have eq3733 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq3737 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3733 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3733
    | exact resolve eq3733 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3761 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3733 X0
       grind)
    | exact superpose eq3733 eq11
    | exact resolve eq11 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3806 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3737 X0
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq3737
    | exact resolve eq3737 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737
  have eq3885 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3806 X0
       grind)
    | exact superpose eq3806 eq11
    | exact resolve eq11 eq3806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3966 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3885 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3885
    | exact resolve eq3885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3885
  have eq4028 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0 X0
       have i₂ := eq3966 (τ X0)
       grind)
    | exact superpose eq3966 eq45
    | exact resolve eq45 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4079 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4028 X0
       have i₂ := eq3806 X0
       grind)
    | exact superpose eq3806 eq4028
    | exact resolve eq4028 eq3806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806 eq4028
  have eq4421 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4449 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4421 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4421
    | exact resolve eq4421 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4421
  have eq4485 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4449 X0
       have i₂ := eq3966 X0
       grind)
    | exact superpose eq3966 eq4449
    | exact resolve eq4449 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4449
  have eq4505 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq4485
  have eq99854 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3666 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3666
    | exact resolve eq3666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99982 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X1) X0
       have i₂ := eq3666 (σ X0) X1
       grind)
    | exact superpose eq3666 eq33
    | (have j1 := eq3666 (σ X0) X1
       grind)
    | exact resolve eq33 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq100109 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq99982 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq99982
    | (have j0 := eq99982 X0 X1
       grind)
    | exact resolve eq99982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99982
  have eq100182 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq99854 X0 X1
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq99854
    | (have j0 := eq99854 X0 X1
       grind)
    | exact resolve eq99854 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99854
  have eq100222 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq100109 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100109
    | (have j0 := eq100109 X0 X1
       grind)
    | exact resolve eq100109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100109
  have eq100309 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq100222 X0 X1
       have i₂ := eq3761 X0
       grind)
    | exact superpose eq3761 eq100222
    | (have j0 := eq100222 X0 X1
       grind)
    | exact resolve eq100222 eq3761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100222
  have eq100360 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq100309 X0 X1
       have i₂ := eq3966 X0
       grind)
    | exact superpose eq3966 eq100309
    | (have j0 := eq100309 X0 X1
       grind)
    | exact resolve eq100309 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100309
  have eq100404 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq100360 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100360
    | (have j0 := eq100360 X0 X1
       grind)
    | exact resolve eq100360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100360
  have eq100626 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq100182 X1 X0
       grind)
    | exact superpose eq100182 eq11
    | (have j1 := eq100182 X1 X0
       grind)
    | exact resolve eq11 eq100182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100182
  have eq100884 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100626 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq100626
    | (have j0 := eq100626 X0 X1
       grind)
    | exact resolve eq100626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100626
  have eq102788 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq100884 X0 (τ X1)
       grind)
    | exact superpose eq100884 eq18
    | (have j1 := eq100884 X0 (τ X1)
       grind)
    | exact resolve eq18 eq100884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq100884
  have eq111585 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq100404 (τ X0) (τ X1)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq100404
    | (have j0 := eq100404 (τ X1) (τ X0)
       grind)
    | exact resolve eq100404 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq100404
  have eq112047 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq111585 X0 X1
       have i₂ := eq4079 X1
       grind)
    | exact superpose eq4079 eq111585
    | (have j0 := eq111585 X0 X1
       grind)
    | exact resolve eq111585 eq4079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111585
  have eq112246 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq112047 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq112047
    | (have j0 := eq112047 X0 X1
       grind)
    | exact resolve eq112047 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112047
  have eq112404 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq112246 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq112246
    | (have j0 := eq112246 X0 X1
       grind)
    | exact resolve eq112246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112246
  have eq112534 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112404 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq112404
    | (have j0 := eq112404 X0 X1
       grind)
    | exact resolve eq112404 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112404
  have eq112627 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112534 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq112534
    | (have j0 := eq112534 X0 X1
       grind)
    | exact resolve eq112534 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112534
  have eq113777 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112627 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112627
  have eq117017 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq102788 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102788
    | exact resolve eq102788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102788
  have eq117371 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq117017 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq117017
    | (have j0 := eq117017 X0 X1
       grind)
    | exact resolve eq117017 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117017
  have eq117868 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq117371 X1 (τ X0)
       grind)
    | exact superpose eq117371 eq19
    | (have j1 := eq117371 X1 (τ X0)
       grind)
    | exact resolve eq19 eq117371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117371
  have eq118230 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117868 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117868
    | (have j0 := eq117868 X0 X1
       grind)
    | exact resolve eq117868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117868
  have eq118399 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118230 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq118230
    | (have j0 := eq118230 X0 X1
       grind)
    | exact resolve eq118230 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq118230
  have eq118534 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118399 X0 X1
       have i₂ := eq4079 X0
       grind)
    | exact superpose eq4079 eq118399
    | (have j0 := eq118399 X0 X1
       grind)
    | exact resolve eq118399 eq4079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4079 eq118399
  have eq132712 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq118534 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq118534
    | (have j0 := eq118534 (σ X1) X0
       grind)
    | exact resolve eq118534 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118534
  have eq132986 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132712 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq132712
    | (have j0 := eq132712 X0 X1
       grind)
    | exact resolve eq132712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132712
  have eq133120 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq132986 X0 X1
       have i₂ := eq3733 X1
       grind)
    | exact superpose eq3733 eq132986
    | (have j0 := eq132986 X0 X1
       grind)
    | exact resolve eq132986 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733 eq132986
  have eq133219 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq133120 X0 X1
       have i₂ := eq3966 X1
       grind)
    | exact superpose eq3966 eq133120
    | (have j0 := eq133120 X0 X1
       grind)
    | exact resolve eq133120 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133120
  have eq133670 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq172
       have i₂ := eq133219 y x
       grind)
    | exact superpose eq133219 eq172
    | (have j1 := eq133219 y x
       grind)
    | (have r₁ := eq172
       have r₂ := eq133219 y x
       grind)
    | exact resolve eq172 eq133219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq133219
  have eq133844 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq133670
  have eq133941 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq186 x y
       grind)
    | (have r₁ := eq133844
       have r₂ := eq186 x y
       grind)
    | exact resolve eq133844 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq133844
  have eq134142 : (σ y) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq133941
       have i₂ := eq3761 x
       grind)
    | exact superpose eq3761 eq133941
    | exact resolve eq133941 eq3761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133941
  have eq134262 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq134142
       have i₂ := eq3966 x
       grind)
    | exact superpose eq3966 eq134142
    | exact resolve eq134142 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134142
  have eq139092 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134262
       grind)
    | exact superpose eq134262 eq16
    | exact resolve eq16 eq134262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139144 : (τ (σ x)) ≠ (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113777 (σ y) (σ x)
       have i₂ := eq134262
       grind)
    | exact superpose eq134262 eq113777
    | (have j0 := eq113777 (σ y) (σ x)
       grind)
    | exact resolve eq113777 eq134262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113777 eq134262
  have eq139147 : (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq139144
  have eq139153 : (σ y) = (σ (k x x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139147
       have i₂ := eq3761 x
       grind)
    | exact superpose eq3761 eq139147
    | exact resolve eq139147 eq3761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3761 eq139147
  have eq139177 : (σ y) = (σ (M.op x x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139153
       have i₂ := eq3966 x
       grind)
    | exact superpose eq3966 eq139153
    | exact resolve eq139153 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966 eq139153
  have eq139178 : (σ y) = (σ (M.op x x)) ∨ (τ (σ x)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x x) := by grind
  clear eq139177
  have eq139197 : (τ (σ x)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139178
       have i₂ := eq33 (σ y) x
       grind)
    | exact superpose eq33 eq139178
    | exact resolve eq139178 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq139178
  have eq139202 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139197
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq139197
    | exact resolve eq139197 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139197
  have eq139206 : x = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139202
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq139202
    | exact resolve eq139202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139202
  have eq139219 : x ≠ x ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq689 y x
       have i₂ := eq139206
       grind)
    | exact superpose eq139206 eq689
    | (have j0 := eq689 y x
       grind)
    | (have r₁ := eq689 y x
       have r₂ := eq139206
       grind)
    | exact resolve eq689 eq139206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq139206
  have eq139239 : x ≠ x ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq139219
  have eq139240 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq139239
  have eq140235 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq139092
       have i₂ := eq139240
       grind)
    | exact superpose eq139240 eq139092
    | exact resolve eq139092 eq139240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139092 eq139240
  have eq140239 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq140235
  have eq140240 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq140239
  have eq141032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4505 x
       have i₂ := eq140240
       grind)
    | exact superpose eq140240 eq4505
    | exact resolve eq4505 eq140240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140240
  have eq141176 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq141032
       have r₂ := eq16
       grind)
    | exact resolve eq141032 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141032
  have eq141230 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq141176
       grind)
    | exact superpose eq141176 eq10
    | exact resolve eq10 eq141176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141176
  have eq141558 : y = (M.op x x) := by
    first
    | (have i₁ := eq141230
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq141230
    | exact resolve eq141230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141230
  have eq142797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4505 x
       have i₂ := eq141558
       grind)
    | exact superpose eq141558 eq4505
    | exact resolve eq4505 eq141558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4505 eq141558
  have eq142942 : False := by grind
  exact eq142942

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq137 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq240 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq241 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq240 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq246 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq241 X0 X1
       have j1 := eq137 X0 X1
       grind)
    | (have r₁ := eq241 X0 X1
       have r₂ := eq137 X0 X1
       grind)
    | (have r₁ := eq241 X1 X1
       have r₂ := eq137 X1 X1
       grind)
    | exact resolve eq241 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq241
  have eq399 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq246 (σ X1) (σ X0)
       grind)
    | exact superpose eq246 eq15
    | exact resolve eq15 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1
       have i₂ := eq246 X1 X0
       grind)
    | exact superpose eq246 eq399
    | exact resolve eq399 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq399
  have eq409 : False := by grind
  exact eq409

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq58
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq265 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq286 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq290 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq286 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq286 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq300 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       have j1 := eq105 X0 (σ X1)
       grind)
    | (have r₁ := eq290 X0 X1
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq290 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq290
  have eq308 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq300
    | (have j0 := eq300 X0 X1
       grind)
    | exact resolve eq300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq309 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq314 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq309 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq309
    | exact resolve eq309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq309 x y
       grind)
    | exact superpose eq309 eq16
    | exact resolve eq16 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq403 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq314 X0 (τ X1)
       grind)
    | exact superpose eq314 eq17
    | exact resolve eq17 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq314
  have eq419 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq403
    | exact resolve eq403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq427 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq419
    | exact resolve eq419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq439 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq325
       have i₂ := eq427 x y
       grind)
    | exact superpose eq427 eq325
    | exact resolve eq325 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq427
  have eq440 : False := by grind
  exact eq440

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pxx_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq209 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq499 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq492 eq14
    | exact resolve eq14 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq493 eq14
    | exact resolve eq14 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq234 eq53
    | exact resolve eq53 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq542 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op (M.op (M.op x y) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq544 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq548 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq53 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq838 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq93 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq850 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq848 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq852 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq838 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq838 X0 X1
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq838 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq838 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq862 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq852 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq852
    | (have j0 := eq852 X0 X1
       grind)
    | exact resolve eq852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq1648 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq492 eq481
    | exact resolve eq481 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1652 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq493 eq481
    | exact resolve eq481 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1864 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq490 X1 X0
       grind)
    | exact superpose eq490 eq14
    | exact resolve eq14 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2618 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq542 (M.op sF0 X0) X0
       have i₂ := eq14 X0 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq14 eq542
    | exact resolve eq542 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq2805 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq544 (M.op sF4 X0) X0
       have i₂ := eq14 X0 sF4 (M.op sF4 X0)
       grind)
    | exact superpose eq14 eq544
    | exact resolve eq544 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq2854 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq534 eq548
    | exact resolve eq548 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq548
  have eq2884 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2854 X0
       have i₂ := eq490 y (M.op x X0)
       grind)
    | exact superpose eq490 eq2854
    | exact resolve eq2854 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq2854
  have eq5427 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq210 eq2618
    | exact resolve eq2618 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq2618
  have eq5490 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq5427
       have i₂ := eq1864 x x
       grind)
    | exact superpose eq1864 eq5427
    | exact resolve eq5427 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5427
  have eq5815 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq219 eq2805
    | exact resolve eq2805 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq2805
  have eq5880 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5815
       have i₂ := eq1864 sF2 sF2
       grind)
    | exact superpose eq1864 eq5815
    | exact resolve eq5815 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5815
  have eq6191 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq2884 eq520
    | exact resolve eq520 eq2884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq6311 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq6191 eq54
    | exact resolve eq54 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq6191
  have eq7366 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq681
    | exact resolve eq681 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq7369 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq681 (M.op X1 X0) X1 X0
       have i₂ := eq52 X1 X1 X0 X0
       grind)
    | exact superpose eq52 eq681
    | exact resolve eq681 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq681
  have eq7490 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7366 X0 X1
       have i₂ := eq1864 X0 X0
       grind)
    | exact superpose eq1864 eq7366
    | exact resolve eq7366 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7366
  have eq7582 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5490 eq7490
    | exact resolve eq7490 eq5490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5490
  have eq7606 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5880 eq7490
    | exact resolve eq7490 eq5880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5880 eq7490
  have eq7693 : x ≠ (M.op x y) ∨ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq7582 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq7582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7582
  have eq7725 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq7693
       have i₂ := eq1864 sF0 sF0
       grind)
    | exact superpose eq1864 eq7693
    | exact resolve eq7693 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7693
  have eq7737 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq7606 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606
  have eq7769 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq7737
       have i₂ := eq1864 sF4 sF4
       grind)
    | exact superpose eq1864 eq7737
    | exact resolve eq7737 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7737
  have eq7864 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq850 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq850
    | (have j0 := eq850 (τ X0)
       grind)
    | exact resolve eq850 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq850
  have eq7872 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7864 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7864
    | (have j0 := eq7864 X0
       grind)
    | exact resolve eq7864 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7864
  have eq7878 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7872 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7872
    | (have j0 := eq7872 X0
       grind)
    | exact resolve eq7872 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7872
  have eq15179 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq15233 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq15179
  have eq15236 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15233
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq15233
    | exact resolve eq15233 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq15233
  have eq15246 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq15236
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq15236 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15236
  have eq15252 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq15246 eq87
    | exact resolve eq87 eq15246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq15246
  have eq15312 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq133
    | (have j0 := eq133 (M.op x y)
       grind)
    | exact resolve eq133 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq15365 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq15312
  have eq15367 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq132 eq15365
    | exact resolve eq15365 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15365
  have eq15379 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq15367
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq15367 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15367
  have eq16933 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq660 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq656 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq656 eq660
    | exact resolve eq660 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq660
  have eq17303 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op (M.op (M.op x y) y) X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq209 eq16933
    | exact resolve eq16933 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq16933
  have eq38827 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op x y) y) y) (M.op x y)) := by
    first
    | exact superpose eq17303 eq520
    | exact resolve eq520 eq17303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520 eq17303
  have eq54711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq54711
    | exact resolve eq54711 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54711
  have eq54727 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq54722
       have r₂ := eq27
       grind)
    | exact resolve eq54722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54722
  have eq54729 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq54727
    | exact resolve eq54727 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54727
  have eq54740 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq54729 eq15252
    | exact resolve eq15252 eq54729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54729
  have eq54875 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq54740
    | exact resolve eq54740 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54740
  have eq54878 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq7878 y
       grind)
    | (have r₁ := eq54875
       have r₂ := eq7878 y
       grind)
    | exact resolve eq54875 eq7878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7878 eq54875
  have eq54879 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq499
       have i₂ := eq54878
       grind)
    | exact superpose eq54878 eq499
    | exact resolve eq499 eq54878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54903 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq54878
       grind)
    | exact superpose eq54878 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq54878
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq54878
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq54878
       grind)
    | exact resolve eq13 eq54878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55008 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54903
  have eq55036 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54879 eq38827
    | exact resolve eq38827 eq54879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38827
  have eq55148 : (M.op y y) = (M.op (M.op y (M.op x y)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54879 eq7369
    | exact resolve eq7369 eq54879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54879
  have eq55158 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq492 eq55148
    | exact resolve eq55148 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55148
  have eq55170 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6311 eq55036
    | exact resolve eq55036 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6311 eq55036
  have eq55313 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq862 y y
       have i₂ := eq55008
       grind)
    | exact superpose eq55008 eq862
    | (have j0 := eq862 y x
       grind)
    | exact resolve eq862 eq55008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq55008
  have eq55314 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55313
  have eq55315 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55314
  have eq55331 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55315
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55315
    | exact resolve eq55315 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55315
  have eq55631 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54878
       have i₂ := eq55158
       grind)
    | exact superpose eq55158 eq54878
    | exact resolve eq54878 eq55158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54878 eq55158
  have eq55747 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq55631
  have eq56150 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55170 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq55170
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq55170
       grind)
    | exact resolve eq13 eq55170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55170
  have eq56255 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq56150
       have r₂ := eq55747
       grind)
    | exact resolve eq56150 eq55747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55747 eq56150
  have eq56263 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55331 eq506
    | exact resolve eq506 eq55331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55331
  have eq56417 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56255 eq132
    | exact resolve eq132 eq56255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq56255
  have eq56468 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15379 eq56417
    | exact resolve eq56417 eq15379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15379 eq56417
  have eq56483 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56468
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq56468
    | exact resolve eq56468 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56468
  have eq56626 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56263 eq7369
    | exact resolve eq7369 eq56263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56263
  have eq56636 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq493 eq56626
    | exact resolve eq56626 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56626
  have eq57453 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56483 eq1864
    | exact resolve eq1864 eq56483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56483
  have eq58445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57453 eq56636
    | exact resolve eq56636 eq57453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56636 eq57453
  have eq58561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq58445
  have eq58568 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq58561
       have r₂ := eq27
       grind)
    | exact resolve eq58561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58561
  have eq58576 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58568 eq27
    | exact resolve eq27 eq58568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58623 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58568 eq1652
    | exact resolve eq1652 eq58568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq58659 : (σ x) ≠ (σ x) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58568 eq7769
    | (have r₁ := eq7769
       have r₂ := eq58568
       grind)
    | exact resolve eq7769 eq58568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7769
  have eq58683 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq58659
  have eq58697 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq58623
    | exact resolve eq58623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58623
  have eq58705 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58568 eq58697
    | exact resolve eq58697 eq58568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58568 eq58697
  have eq58833 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq58705
  have eq59101 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58833 eq1864
    | exact resolve eq1864 eq58833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59281 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59101 eq15252
    | exact resolve eq15252 eq59101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59101
  have eq59416 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq59281
    | exact resolve eq59281 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq59281
  have eq62460 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58833 eq58683
    | exact resolve eq58683 eq58833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58683 eq58833
  have eq62479 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq62460
  have eq62482 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62479 eq113
    | exact resolve eq113 eq62479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq62479
  have eq62500 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq62482
  have eq62507 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq62500
       have r₂ := eq58576
       grind)
    | exact resolve eq62500 eq58576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58576 eq62500
  have eq62598 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq499
       have i₂ := eq62507
       grind)
    | exact superpose eq62507 eq499
    | exact resolve eq499 eq62507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq62624 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq62507
       grind)
    | exact superpose eq62507 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq62507
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq62507
       grind)
    | exact resolve eq13 eq62507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62729 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq62624
  have eq62874 : (M.op y y) = (M.op (M.op y (M.op x y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62598 eq7369
    | exact resolve eq7369 eq62598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62598
  have eq62886 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq492 eq62874
    | exact resolve eq62874 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq62874
  have eq63053 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59416
       have i₂ := eq62729
       grind)
    | exact superpose eq62729 eq59416
    | exact resolve eq59416 eq62729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59416 eq62729
  have eq63086 : x = (M.op x y) ∨ x = y := by grind
  clear eq63053
  have eq64442 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62507
       have i₂ := eq62886
       grind)
    | exact superpose eq62886 eq62507
    | exact resolve eq62507 eq62886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62507 eq62886
  have eq64559 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq64442
  have eq64738 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq64559
  have eq64743 : x = (M.op x y) := by
    first
    | (have r₁ := eq64738
       have r₂ := eq63086
       grind)
    | exact resolve eq64738 eq63086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63086 eq64738
  have eq64950 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq64743 eq20
    | exact resolve eq20 eq64743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq65043 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq64743 eq1648
    | exact resolve eq1648 eq64743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq65079 : x ≠ x ∨ x = (k (M.op x x) x) := by
    first
    | exact superpose eq64743 eq7725
    | (have r₁ := eq7725
       have r₂ := eq64743
       grind)
    | exact resolve eq7725 eq64743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7725
  have eq65109 : x = (k (M.op x x) x) := by grind
  clear eq65079
  have eq65132 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq65043
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65043
    | exact resolve eq65043 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq65043
  have eq65181 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq64950
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq64950
    | exact resolve eq64950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64950
  have eq65190 : y = (M.op x x) := by
    first
    | exact superpose eq64743 eq65132
    | exact resolve eq65132 eq64743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64743 eq65132
  have eq65441 : x = (M.op y y) := by
    first
    | (have i₁ := eq1864 x x
       have i₂ := eq65190
       grind)
    | exact superpose eq65190 eq1864
    | exact resolve eq1864 eq65190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq66646 : x = (k y x) := by
    first
    | (have i₁ := eq65109
       have i₂ := eq65190
       grind)
    | exact superpose eq65190 eq65109
    | exact resolve eq65109 eq65190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65109 eq65190
  have eq66665 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq849 x y
       have i₂ := eq66646
       grind)
    | exact superpose eq66646 eq849
    | (have j0 := eq849 y y
       grind)
    | exact resolve eq849 eq66646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq66646
  have eq66668 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq66665
  have eq66672 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66668
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66668
    | exact resolve eq66668 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66668
  have eq66692 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq66672
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66672
    | exact resolve eq66672 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66672
  have eq66710 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq66692
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66692
    | exact resolve eq66692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66692
  have eq66728 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq66710
    | exact resolve eq66710 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq66710
  have eq66740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq65181 eq66728
    | exact resolve eq66728 eq65181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66728
  have eq66749 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq66740
       have r₂ := eq27
       grind)
    | exact resolve eq66740 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66740
  have eq66821 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq66749 eq506
    | exact resolve eq506 eq66749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq66830 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq66749 eq15252
    | exact resolve eq15252 eq66749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15252
  have eq66985 : y = (k y y) := by
    first
    | exact superpose eq29 eq66830
    | exact resolve eq66830 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq66830
  have eq67128 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq66821 eq7369
    | exact resolve eq7369 eq66821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7369 eq66821
  have eq67139 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq493 eq67128
    | exact resolve eq67128 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq67128
  have eq67173 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66749 eq67139
    | exact resolve eq67139 eq66749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66749 eq67139
  have eq67178 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq67173 eq27
    | exact resolve eq27 eq67173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq67173
  have eq67449 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq66985
       grind)
    | exact superpose eq66985 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq66985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66985
  have eq67472 : y = (M.op y y) := by grind
  clear eq67449
  have eq67487 : x = y := by
    first
    | (have i₁ := eq67472
       have i₂ := eq65441
       grind)
    | exact superpose eq65441 eq67472
    | exact resolve eq67472 eq65441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65441 eq67472
  have eq67515 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq67487
       grind)
    | exact superpose eq67487 eq24
    | exact resolve eq24 eq67487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq67487
  have eq67794 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq67515
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq67515
    | exact resolve eq67515 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq67515
  have eq67893 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq65181 eq67794
    | exact resolve eq67794 eq65181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65181 eq67794
  have eq67980 : False := by grind
  exact eq67980

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq420 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq56
  have eq745 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1652 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq419 eq410
    | exact resolve eq410 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq1656 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq420 eq410
    | exact resolve eq410 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq420
  have eq54956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq54956
    | exact resolve eq54956 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54956
  have eq54972 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq54967
       have r₂ := eq28
       grind)
    | exact resolve eq54967 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54967
  have eq54974 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq54972
    | exact resolve eq54972 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54972
  have eq55002 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq54974
  have eq55115 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq55002
    | exact resolve eq55002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55002
  have eq56000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq55115 eq114
    | exact resolve eq114 eq55115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55115
  have eq56015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56000
  have eq56017 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq56015
       have r₂ := eq28
       grind)
    | exact resolve eq56015 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56015
  have eq56047 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56017
  have eq56160 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56047
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56047
    | exact resolve eq56047 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56047
  have eq57051 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq56160
       grind)
    | exact superpose eq56160 eq73
    | exact resolve eq73 eq56160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56160
  have eq57085 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq57051
    | exact resolve eq57051 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57051
  have eq57243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57085 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq57085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq57243
    | exact resolve eq57243 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57243
  have eq57261 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq57256
       have r₂ := eq28
       grind)
    | exact resolve eq57256 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57256
  have eq57263 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq57261
    | exact resolve eq57261 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57261
  have eq57264 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq57263
  have eq57293 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq57264
  have eq57406 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq57293
    | exact resolve eq57293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57293
  have eq57942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57406 eq57085
    | exact resolve eq57085 eq57406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57085 eq57406
  have eq57954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57942
  have eq57958 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq57954
       have r₂ := eq28
       grind)
    | exact resolve eq57954 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57954
  have eq58007 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57958 eq1656
    | exact resolve eq1656 eq57958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656
  have eq58068 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq58007
    | exact resolve eq58007 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58007
  have eq58078 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57958 eq58068
    | exact resolve eq58068 eq57958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57958 eq58068
  have eq58202 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq58078
  have eq58362 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq58202
  have eq58475 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq58362
    | exact resolve eq58362 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58362
  have eq58760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58475 eq114
    | exact resolve eq114 eq58475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq58774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq58760
  have eq58777 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq58774
       have r₂ := eq28
       grind)
    | exact resolve eq58774 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58774
  have eq58808 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq58777
  have eq58921 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58808
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58808
    | exact resolve eq58808 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58808
  have eq59454 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq58921
       grind)
    | exact superpose eq58921 eq73
    | exact resolve eq73 eq58921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58921
  have eq59488 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq59454
    | exact resolve eq59454 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59454
  have eq59542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59488 eq58475
    | exact resolve eq58475 eq59488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58475 eq59488
  have eq59554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq59542
  have eq59560 : x = (M.op x y) := by
    first
    | (have r₁ := eq59554
       have r₂ := eq28
       grind)
    | exact resolve eq59554 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59554
  have eq59565 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq59560 eq21
    | exact resolve eq21 eq59560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq59663 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59560 eq1652
    | exact resolve eq1652 eq59560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq59724 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq59663
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59663
    | exact resolve eq59663 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59663
  have eq59783 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq59565
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59565
    | exact resolve eq59565 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59565
  have eq59792 : y = (M.op x x) := by
    first
    | exact superpose eq59560 eq59724
    | exact resolve eq59724 eq59560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59724
  have eq59799 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq59783 eq27
    | exact resolve eq27 eq59783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59924 : (M.op x y) = (k y x) := by grind
  clear eq59792
  have eq60046 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq59924
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59924
    | exact resolve eq59924 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq59924
  have eq60069 : x = (k y x) := by
    first
    | exact superpose eq59560 eq60046
    | exact resolve eq60046 eq59560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59560 eq60046
  have eq60370 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq60069
       grind)
    | exact superpose eq60069 eq73
    | exact resolve eq73 eq60069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq60387 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq745 x y
       have i₂ := eq60069
       grind)
    | exact superpose eq60069 eq745
    | (have j0 := eq745 x y
       grind)
    | exact resolve eq745 eq60069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq60069
  have eq60391 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq60387
  have eq60400 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60391
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq60391
    | exact resolve eq60391 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60391
  have eq60414 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq59783 eq60370
    | exact resolve eq60370 eq59783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60370
  have eq60417 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60400
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60400
    | exact resolve eq60400 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60400
  have eq60431 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq60414
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60414
    | exact resolve eq60414 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60414
  have eq60434 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq60417
    | exact resolve eq60417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60417
  have eq60447 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq59783 eq60431
    | exact resolve eq60431 eq59783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60431
  have eq60450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59783 eq60434
    | exact resolve eq60434 eq59783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60434
  have eq60460 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq60450
       have r₂ := eq28
       grind)
    | exact resolve eq60450 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60450
  have eq60470 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq60460
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60460
    | exact resolve eq60460 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq60460
  have eq60479 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq59783 eq60470
    | exact resolve eq60470 eq59783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59783 eq60470
  have eq60488 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq60479
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq60479
    | exact resolve eq60479 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq60479
  have eq60846 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq60488
  have eq60968 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq59799 eq60846
    | exact resolve eq60846 eq59799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59799 eq60846
  have eq60969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60447 eq60968
    | exact resolve eq60968 eq60447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60447 eq60968
  have eq60970 : False := by grind
  exact eq60970

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
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
  have eq177 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq192 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq177
       grind)
    | exact superpose eq177 eq40
    | exact resolve eq40 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq193 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq192
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq192
    | exact resolve eq192 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq195 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq193
    | exact resolve eq193 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq195 eq178
    | exact resolve eq178 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq195
  have eq202 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq199
       have r₂ := eq27
       grind)
    | exact resolve eq199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq205 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq202 eq32
    | exact resolve eq32 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq202
  have eq222 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq205
    | exact resolve eq205 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq205
  have eq223 : x = y := by grind
  clear eq222
  have eq227 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq223
       grind)
    | exact superpose eq223 eq18
    | exact resolve eq18 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq228 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq223
       grind)
    | exact superpose eq223 eq24
    | exact resolve eq24 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq223
  have eq229 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq228
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228
    | exact resolve eq228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq232 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq229 eq26
    | exact resolve eq26 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq229
  have eq382 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq382 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq382 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq382 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq382 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq382 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq640 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq227
       have i₂ := eq383 x
       grind)
    | exact superpose eq383 eq227
    | exact resolve eq227 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq653 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq232
       have i₂ := eq383 sF2
       grind)
    | exact superpose eq383 eq232
    | exact resolve eq232 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq383
  have eq703 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq640
       grind)
    | exact superpose eq640 eq40
    | exact resolve eq40 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq640
  have eq704 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq703
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq703
    | exact resolve eq703 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq703
  have eq706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq653 eq704
    | exact resolve eq704 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq704
  have eq708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq706
    | exact resolve eq706 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq706
  have eq710 : False := by grind
  exact eq710

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_y_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1 x (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X1 (M.op X0 X0)
       have i₂ := eq121 X0 X0
       grind)
    | exact superpose eq121 eq121
    | exact resolve eq121 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X0
       have i₂ := eq121 X1 X0
       grind)
    | exact superpose eq121 eq9
    | exact resolve eq9 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq121 X0 X0
       grind)
    | exact superpose eq121 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq137 X0 X1
       grind)
    | exact superpose eq137 eq9
    | exact resolve eq9 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq51 X1 x x X0
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq52 X1 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X0 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X0 X0) X2
       have i₂ := eq214 X0 X1
       grind)
    | exact superpose eq214 eq52
    | exact resolve eq52 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X0 X2) X5) (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0) X5
       have i₂ := eq51 X1 x x X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0 x (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq137 (M.op X0 X1) (M.op (M.op X0 x) X1)
       grind)
    | exact superpose eq137 eq53
    | exact resolve eq53 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq382 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq53 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154 y x
       grind)
    | exact superpose eq154 eq16
    | (have j1 := eq154 y y
       grind)
    | exact resolve eq16 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op (σ X1) X2) (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq154 X0 X1
       grind)
    | exact superpose eq154 eq9
    | (have j1 := eq154 X0 X0
       grind)
    | exact resolve eq9 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq154 X0 X0
       grind)
    | exact superpose eq154 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq154 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq154 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq154 X0 X1
       grind)
    | exact resolve eq12 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq154 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq498 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq497 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq500 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq495 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq506 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq500 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq500 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq640 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op (M.op X0 X0) X1) x X0
       have i₂ := eq290 X0 (M.op (M.op (M.op (M.op X0 X0) X1) x) X0) X1
       grind)
    | exact superpose eq290 eq53
    | exact resolve eq53 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq683 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq640 (M.op X1 X1) X1
       have i₂ := eq121 X1 X1
       grind)
    | exact superpose eq121 eq640
    | exact resolve eq640 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq767 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq683 (M.op X0 X1) X2
       grind)
    | exact superpose eq683 eq53
    | exact resolve eq53 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq769 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) (M.op X0 X0)
       have i₂ := eq683 X0 X1
       grind)
    | exact superpose eq683 eq9
    | exact resolve eq9 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1349 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq230 (M.op X1 X0) X1 X0
       have i₂ := eq769 X1 (M.op X1 X0) X0
       grind)
    | exact superpose eq769 eq230
    | exact resolve eq230 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq769
  have eq1674 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X1 (M.op (M.op X0 X1) X3)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq382 X0 (M.op (M.op X1 x) (M.op X1 X0)) x
       have i₂ := eq52 X0 X1 x
       grind)
    | exact superpose eq52 eq382
    | exact resolve eq382 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1706 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq382 (M.op X1 X0) X1 X0
       have i₂ := eq51 X1 X1 X0 X0
       grind)
    | exact superpose eq51 eq382
    | exact resolve eq382 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1712 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 X1 X0 (M.op X0 X1)
       have i₂ := eq237 X1 X0 X1
       grind)
    | exact superpose eq237 eq382
    | exact resolve eq382 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq1826 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op (M.op (M.op X1 X0) X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X0
       have i₂ := eq1706 X0 X1
       grind)
    | exact superpose eq1706 eq9
    | exact resolve eq9 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq1873 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq498 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq498
    | (have j0 := eq498 (τ X0)
       grind)
    | exact resolve eq498 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq1883 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1873 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1873
    | (have j0 := eq1873 X0
       grind)
    | exact resolve eq1873 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq1890 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1883 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1883
    | (have j0 := eq1883 X0
       grind)
    | exact resolve eq1883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1902 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq506 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq506
    | (have j0 := eq506 (τ X0) X1
       grind)
    | exact resolve eq506 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1912 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1902 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1902
    | (have j0 := eq1902 X0 X1
       grind)
    | exact resolve eq1902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq1919 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1912 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1912
    | (have j0 := eq1912 X0 X1
       grind)
    | exact resolve eq1912 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912
  have eq1924 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1919 (τ X0) X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq1919
    | (have j0 := eq1919 (τ X0) X1
       grind)
    | exact resolve eq1919 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1919
  have eq5067 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X0 X1) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X2 (M.op X1 X0)
       have i₂ := eq1712 X1 X0
       grind)
    | (have i₁ := eq121 X0 (M.op X0 X0)
       have i₂ := eq1712 X0 X0
       grind)
    | exact superpose eq1712 eq121
    | exact resolve eq121 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5956 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X1 X0) X2) X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq334 X1 (M.op (M.op (M.op X1 X0) X2) X0) X0 X0
       have i₂ := eq238 X0 (M.op X1 X0) X2 X1
       grind)
    | exact superpose eq238 eq334
    | exact resolve eq334 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq334
  have eq6543 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5956 X0 X1 (M.op X0 X1)
       have i₂ := eq1712 X0 X1
       grind)
    | (have i₁ := eq5956 X1 X0 (M.op X0 X1)
       have i₂ := eq1712 X0 X1
       grind)
    | exact superpose eq1712 eq5956
    | exact resolve eq5956 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq7493 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X2 (M.op X0 X1)) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1826 (M.op X0 X1) X2 X1
       have i₂ := eq381 X0 X1
       grind)
    | exact superpose eq381 eq1826
    | exact resolve eq1826 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq7519 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op X2 X0) X2) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1826 X0 X2 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq141 (M.op X0 X0) X1
       grind)
    | exact superpose eq141 eq1826
    | exact resolve eq1826 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1826
  have eq7780 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op (M.op X2 X0) X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7519 X1 X1 X2
       have i₂ := eq121 X1 X1
       grind)
    | exact superpose eq121 eq7519
    | exact resolve eq7519 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7519
  have eq12378 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq470
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq470
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq470 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq12379 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq12378
  have eq19749 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op X0 (σ X1)) (σ (k X1 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq472 X1 X1 (M.op X0 (σ X1))
       have i₂ := eq70 (σ X1) X0
       grind)
    | exact superpose eq70 eq472
    | (have j0 := eq472 X1 X1 x
       grind)
    | exact resolve eq472 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq19948 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op X0 (σ X1)) (σ (k X1 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq19749 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19749
  have eq55706 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X1)) (M.op (M.op X1 X0) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X1 X0) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5956 (M.op (M.op X1 X0) (M.op X0 X1)) X2 (M.op X0 X1)
       have i₂ := eq5067 X1 X0 (M.op X2 (M.op (M.op X1 X0) (M.op X0 X1)))
       grind)
    | exact superpose eq5067 eq5956
    | exact resolve eq5956 eq5067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5956
  have eq56122 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X1 X0) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55706 X0 X1 X2
       have i₂ := eq5067 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq5067 eq55706
    | exact resolve eq55706 eq5067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5067 eq55706
  have eq74248 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq371 X2 X0 X1 (M.op (M.op X1 X0) (M.op X0 X1)) X3
       have i₂ := eq56122 X0 X1 X2
       grind)
    | exact superpose eq56122 eq371
    | exact resolve eq371 eq56122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq56122
  have eq91627 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3) X0)) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7493 X1 X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3) X0)
       have i₂ := eq74248 X1 X2 X0 X3
       grind)
    | exact superpose eq74248 eq7493
    | exact resolve eq7493 eq74248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7493 eq74248
  have eq91929 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91627 X0 X1 X2 X3
       have i₂ := eq70 X0 (M.op (M.op (M.op X1 X2) (M.op X1 X0)) X3)
       grind)
    | exact superpose eq70 eq91627
    | exact resolve eq91627 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq91627
  have eq105078 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1674 (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X1 X0) X0
       have i₂ := eq91929 X0 X1 X2 (M.op X1 X0)
       grind)
    | exact superpose eq91929 eq1674
    | exact resolve eq1674 eq91929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91929
  have eq136842 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19948 X1 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq19948
    | (have j0 := eq19948 X0 (τ X0)
       grind)
    | exact resolve eq19948 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19948
  have eq137364 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq136842 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136842
    | (have j0 := eq136842 X0 X1
       grind)
    | exact resolve eq136842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136842
  have eq137374 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq137364 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq137364
    | (have j0 := eq137364 X0 X1
       grind)
    | exact resolve eq137364 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137364
  have eq137602 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq137374 X0 (M.op (M.op (M.op (k X0 X0) X0) (M.op (k X0 X0) X0)) (k X0 X0))
       have i₂ := eq6543 (k X0 X0) X0
       grind)
    | exact superpose eq6543 eq137374
    | (have j0 := eq137374 X0 x
       grind)
    | exact resolve eq137374 eq6543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6543 eq137374
  have eq138334 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq214 (k X0 X0) (k X0 X0)
       have i₂ := eq137602 X0
       grind)
    | exact superpose eq137602 eq214
    | (have j1 := eq137602 X0
       grind)
    | exact resolve eq214 eq137602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137602
  have eq138604 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq138334 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq138334 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq138334 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138334
  have eq138612 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq506 X0 X1
       have i₂ := eq138604 X0
       grind)
    | exact superpose eq138604 eq506
    | (have j0 := eq506 X0 X1
       grind)
    | exact resolve eq506 eq138604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq138619 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1924 X0 X1
       have i₂ := eq138604 X0
       grind)
    | exact superpose eq138604 eq1924
    | (have j0 := eq1924 X0 X1
       grind)
    | exact resolve eq1924 eq138604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924
  have eq138645 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq138604 (σ X0)
       grind)
    | exact superpose eq138604 eq15
    | exact resolve eq15 eq138604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138683 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq138645 X0
       have i₂ := eq138604 X0
       grind)
    | exact superpose eq138604 eq138645
    | exact resolve eq138645 eq138604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138604 eq138645
  have eq139201 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq153 (σ X0) X1
       have i₂ := eq138683 X0
       grind)
    | exact superpose eq138683 eq153
    | exact resolve eq153 eq138683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139206 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq683 (σ X0) X1
       have i₂ := eq138683 X0
       grind)
    | exact superpose eq138683 eq683
    | exact resolve eq683 eq138683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq139352 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq382 (σ X0) (σ X0) x
       have i₂ := eq138683 X0
       grind)
    | exact superpose eq138683 eq382
    | exact resolve eq382 eq138683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq520863 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12379
       have i₂ := eq138683 y
       grind)
    | exact superpose eq138683 eq12379
    | exact resolve eq12379 eq138683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12379
  have eq520864 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq520863
       have i₂ := eq138683 x
       grind)
    | exact superpose eq138683 eq520863
    | exact resolve eq520863 eq138683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520863
  have eq528385 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq520864
       grind)
    | exact superpose eq520864 eq10
    | exact resolve eq10 eq520864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520864
  have eq528600 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq528385
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq528385
    | exact resolve eq528385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528385
  have eq528601 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq528600
  have eq528683 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq528601
       grind)
    | exact superpose eq528601 eq10
    | exact resolve eq10 eq528601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528601
  have eq528898 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq528683
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq528683
    | exact resolve eq528683 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528683
  have eq528899 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq528898
  have eq528925 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq153 y x
       have i₂ := eq528899
       grind)
    | exact superpose eq528899 eq153
    | (have r₁ := eq153 y x
       have r₂ := eq528899
       grind)
    | (have r₁ := eq153 x x
       have r₂ := eq528899
       grind)
    | exact resolve eq153 eq528899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528997 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq138612 y X0
       have i₂ := eq528899
       grind)
    | exact superpose eq528899 eq138612
    | (have j0 := eq138612 y X0
       grind)
    | exact resolve eq138612 eq528899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138612
  have eq529000 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (M.op X0 X0) = (k X0 (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq138619 y X0
       have i₂ := eq528899
       grind)
    | exact superpose eq528899 eq138619
    | (have j0 := eq138619 y X0
       grind)
    | exact resolve eq138619 eq528899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138619
  have eq529076 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (M.op (σ y) X0)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq139352 y x
       have i₂ := eq528899
       grind)
    | exact superpose eq528899 eq139352
    | exact resolve eq139352 eq528899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529291 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (M.op y X0)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1674 y y x
       have i₂ := eq528899
       grind)
    | exact superpose eq528899 eq1674
    | exact resolve eq1674 eq528899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq529449 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op (M.op y y) (M.op X0 y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7780 y X0 y
       have i₂ := eq528899
       grind)
    | exact superpose eq528899 eq7780
    | exact resolve eq7780 eq528899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7780
  have eq529619 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq529000 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529000
  have eq529622 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq528997 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528997
  have eq529624 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq528925 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528925
  have eq529677 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq529449 X0
       have i₂ := eq214 y X0
       grind)
    | exact superpose eq214 eq529449
    | exact resolve eq529449 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq529449
  have eq529694 : ∀ X0 : G, (M.op X0 X0) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq529291 X0
       have i₂ := eq1349 X0 y
       grind)
    | exact superpose eq1349 eq529291
    | exact resolve eq529291 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529291
  have eq529722 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq529076 X0
       have i₂ := eq1349 X0 (σ y)
       grind)
    | exact superpose eq1349 eq529076
    | exact resolve eq529076 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529076
  have eq538637 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq529677 X1
       have i₂ := eq529677 X0
       grind)
    | (have i₁ := eq529677 X0
       have i₂ := eq529677 y
       grind)
    | exact superpose eq529677 eq529677
    | exact resolve eq529677 eq529677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529677
  have eq540684 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq538637 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538637
  have eq541092 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq529624 X0
       have i₂ := eq529694 X0
       grind)
    | (have i₁ := eq529624 y
       have i₂ := eq529694 y
       grind)
    | exact superpose eq529694 eq529624
    | exact resolve eq529624 eq529694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529624
  have eq542988 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq541092 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541092
  have eq664923 : ∀ X0 : G, (k (M.op X0 X0) (τ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq529619 (M.op X0 X0)
       have i₂ := eq121 X0 X0
       grind)
    | exact superpose eq121 eq529619
    | exact resolve eq529619 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529619
  have eq667416 : ∀ X0 : G, (k X0 (σ y)) = (M.op y X0) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq529694 X0
       have i₂ := eq529622 X0
       grind)
    | exact superpose eq529622 eq529694
    | exact resolve eq529694 eq529622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529622 eq529694
  have eq669018 : ∀ X0 : G, (k X0 (σ y)) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq667416 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667416
  have eq669407 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq529722 (M.op X0 X0)
       have i₂ := eq121 X0 X0
       grind)
    | exact superpose eq121 eq529722
    | exact resolve eq529722 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq529722
  have eq679984 : y = (k y (τ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq664923 y
       have i₂ := eq528899
       grind)
    | exact superpose eq528899 eq664923
    | exact resolve eq664923 eq528899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528899 eq664923
  have eq679998 : y = (k y (τ y)) ∨ x = (M.op x x) := by grind
  clear eq679984
  have eq680077 : (σ y) = (k (σ y) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq679998
       grind)
    | exact superpose eq679998 eq18
    | exact resolve eq18 eq679998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq679998
  have eq680143 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq542988 (σ y)
       have i₂ := eq680077
       grind)
    | exact superpose eq680077 eq542988
    | exact resolve eq542988 eq680077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542988 eq680077
  have eq680153 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x x) := by grind
  clear eq680143
  have eq706115 : (σ y) ≠ (M.op y (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1890 (σ y)
       have i₂ := eq669018 (σ y)
       grind)
    | exact superpose eq669018 eq1890
    | (have j0 := eq1890 (σ y)
       grind)
    | exact resolve eq1890 eq669018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890 eq669018
  have eq706196 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq706115
       have r₂ := eq680153
       grind)
    | exact resolve eq706115 eq680153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680153 eq706115
  have eq706210 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq706196
       have i₂ := eq138683 y
       grind)
    | exact superpose eq138683 eq706196
    | exact resolve eq706196 eq138683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138683 eq706196
  have eq706226 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq706210
       have i₂ := eq540684 y X0
       grind)
    | (have i₁ := eq706210
       have i₂ := eq540684 X0 y
       grind)
    | exact superpose eq540684 eq706210
    | exact resolve eq706210 eq540684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540684 eq706210
  have eq706402 : ∀ X0 : G, (σ y) = (σ (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq706226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706226
  have eq710497 : ∀ X0 : G, (σ y) = (M.op X0 (σ (M.op y y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq139206 y (M.op X0 X0)
       have i₂ := eq669407 X0
       grind)
    | exact superpose eq669407 eq139206
    | exact resolve eq139206 eq669407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139206 eq669407
  have eq1068668 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq710497 X0
       have i₂ := eq706402 y
       grind)
    | exact superpose eq706402 eq710497
    | exact resolve eq710497 eq706402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710497
  have eq1071041 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1068668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068668
  have eq1073610 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1071041 (σ x)
       grind)
    | exact superpose eq1071041 eq16
    | exact resolve eq16 eq1071041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071041
  have eq1073958 : x = (M.op x x) := by
    first
    | (have r₁ := eq1073610
       have r₂ := eq706402 x
       grind)
    | exact resolve eq1073610 eq706402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706402 eq1073610
  have eq1074217 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq153 x x
       have i₂ := eq1073958
       grind)
    | exact superpose eq1073958 eq153
    | (have r₁ := eq153 x x
       have r₂ := eq1073958
       grind)
    | exact resolve eq153 eq1073958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq1074337 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq139201 x x
       have i₂ := eq1073958
       grind)
    | exact superpose eq1073958 eq139201
    | exact resolve eq139201 eq1073958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139201
  have eq1074368 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (M.op (σ x) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq139352 x x
       have i₂ := eq1073958
       grind)
    | exact superpose eq1073958 eq139352
    | exact resolve eq139352 eq1073958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139352
  have eq1075083 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x (M.op x X0)) (M.op x X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq105078 X0 x x
       have i₂ := eq1073958
       grind)
    | exact superpose eq1073958 eq105078
    | exact resolve eq105078 eq1073958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105078 eq1073958
  have eq1075096 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq1074337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074337
  have eq1075103 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1074217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074217
  have eq1075109 : ∀ X0 : G, (M.op X0 X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1075083 X0
       have i₂ := eq767 x (M.op x X0) X0
       grind)
    | exact superpose eq767 eq1075083
    | exact resolve eq1075083 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq1075083
  have eq1075256 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq1074368 X0
       have i₂ := eq1349 X0 (σ x)
       grind)
    | exact superpose eq1349 eq1074368
    | exact resolve eq1074368 eq1349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349 eq1074368
  have eq1082553 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1075109 X0
       have i₂ := eq1075103 X0
       grind)
    | exact superpose eq1075103 eq1075109
    | exact resolve eq1075109 eq1075103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1193114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq1075096 (σ X0)
       grind)
    | exact superpose eq1075096 eq15
    | exact resolve eq15 eq1075096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075096
  have eq1193147 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1193114 X0
       have i₂ := eq1082553 X0
       grind)
    | exact superpose eq1082553 eq1193114
    | exact resolve eq1193114 eq1082553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193114
  have eq1193542 : ∀ X0 : G, (k (σ X0) x) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1193147 X0
       have i₂ := eq1075103 (σ X0)
       grind)
    | exact superpose eq1075103 eq1193147
    | exact resolve eq1193147 eq1075103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075103 eq1193147
  have eq1193842 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1193542 X0
       have i₂ := eq1082553 (σ X0)
       grind)
    | exact superpose eq1082553 eq1193542
    | exact resolve eq1193542 eq1082553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082553 eq1193542
  have eq1197203 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1075256 X0
       have i₂ := eq1075109 X0
       grind)
    | (have i₁ := eq1075256 x
       have i₂ := eq1075109 x
       grind)
    | exact superpose eq1075109 eq1075256
    | exact resolve eq1075256 eq1075109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075109 eq1075256
  have eq1276224 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1197203 (σ y)
       grind)
    | exact superpose eq1197203 eq16
    | exact resolve eq16 eq1197203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197203
  have eq1387389 : False := by grind
  exact eq1387389
