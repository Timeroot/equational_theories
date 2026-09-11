import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation419`: `x = x ◇ (x ◇ (y ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq18
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq25
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1026 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq209
    | (have j0 := eq209 (σ X1) (σ X0)
       grind)
    | exact resolve eq209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq5947 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq87 X1 X0
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq87 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq87 (σ X1) X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5979 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq5980 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5979 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5979
  have eq5982 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5947 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5947
  have eq5983 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5982 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5982
  have eq5987 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5980 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5980
    | (have j0 := eq5980 X0
       grind)
    | exact resolve eq5980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5980
  have eq6036 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq5987 X0
       grind)
    | exact superpose eq5987 eq39
    | (have j1 := eq5987 X0
       grind)
    | exact resolve eq39 eq5987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5987
  have eq6073 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6036 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6036
    | (have j0 := eq6036 X0
       grind)
    | exact resolve eq6036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036
  have eq6074 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6073 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6073
  have eq6078 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6074 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6074
    | exact resolve eq6074 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq6074 X0
       grind)
    | exact superpose eq6074 eq11
    | exact resolve eq11 eq6074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6074
  have eq6176 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6078 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq6078
    | exact resolve eq6078 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6078
  have eq6462 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq6176 X0
       grind)
    | exact superpose eq6176 eq11
    | exact resolve eq11 eq6176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6176
  have eq6575 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq6462 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq6462
    | exact resolve eq6462 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6462
  have eq7086 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq7149 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq7086 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq7086
    | exact resolve eq7086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7086
  have eq7195 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7149 X0
       have i₂ := eq6575 X0
       grind)
    | exact superpose eq6575 eq7149
    | exact resolve eq7149 eq6575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7149
  have eq7225 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq7195
  have eq32353 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1026 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq1026
    | (have j0 := eq1026 (τ X0) (τ X1)
       grind)
    | exact resolve eq1026 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq32439 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32353 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq32353
    | (have j0 := eq32353 X0 X1
       grind)
    | exact resolve eq32353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32353
  have eq32497 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32439 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32439
    | (have j0 := eq32439 X0 X1
       grind)
    | exact resolve eq32439 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32439
  have eq32554 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32497 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32497
    | (have j0 := eq32497 X0 X1
       grind)
    | exact resolve eq32497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32497
  have eq32608 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq32554 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq32554
    | (have j0 := eq32554 X0 X1
       grind)
    | exact resolve eq32554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32554
  have eq32655 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32608 X0 X1
       have i₂ := eq6108 (σ (τ X1))
       grind)
    | exact superpose eq6108 eq32608
    | (have j0 := eq32608 X0 X1
       grind)
    | exact resolve eq32608 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32608
  have eq32700 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32655 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq32655
    | (have j0 := eq32655 X0 X1
       grind)
    | exact resolve eq32655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32655
  have eq32740 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32700 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq32700
    | (have j0 := eq32700 X0 X1
       grind)
    | exact resolve eq32700 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32700
  have eq32776 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32740 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq32740
    | (have j0 := eq32740 X0 X1
       grind)
    | exact resolve eq32740 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32740
  have eq32803 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32776 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32776
    | (have j0 := eq32776 X0 X1
       grind)
    | exact resolve eq32776 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32776
  have eq32826 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32803 X0 X1
       have i₂ := eq6575 X1
       grind)
    | exact superpose eq6575 eq32803
    | (have j0 := eq32803 X0 X1
       grind)
    | exact resolve eq32803 eq6575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32803
  have eq41338 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq5983 X0 X1
       grind)
    | exact superpose eq5983 eq31
    | (have j1 := eq5983 X0 X1
       grind)
    | exact resolve eq31 eq5983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5983
  have eq41544 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq41338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41338
    | (have j0 := eq41338 X0 X1
       grind)
    | exact resolve eq41338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41338
  have eq43686 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41544 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41544
    | (have j0 := eq41544 (τ X0) X1
       grind)
    | exact resolve eq41544 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43747 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq41544 X0 X1
       grind)
    | exact superpose eq41544 eq11
    | (have j1 := eq41544 X0 X1
       grind)
    | exact resolve eq11 eq41544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41544
  have eq43872 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43747 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq43747
    | (have j0 := eq43747 X0 X1
       grind)
    | exact resolve eq43747 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq43747
  have eq43907 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43686 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq43686
    | (have j0 := eq43686 X0 X1
       grind)
    | exact resolve eq43686 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43686
  have eq43946 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43907 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq43907
    | (have j0 := eq43907 X0 X1
       grind)
    | exact resolve eq43907 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq43907
  have eq44797 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq43872 X1 (σ X0)
       grind)
    | exact superpose eq43872 eq15
    | (have j1 := eq43872 X1 (σ X0)
       grind)
    | exact resolve eq15 eq43872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43872
  have eq44929 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44797 X0 X1
       have i₂ := eq6108 X0
       grind)
    | exact superpose eq6108 eq44797
    | (have j0 := eq44797 X0 X1
       grind)
    | exact resolve eq44797 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108 eq44797
  have eq44982 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44929 X0 X1
       have i₂ := eq6575 X0
       grind)
    | exact superpose eq6575 eq44929
    | (have j0 := eq44929 X0 X1
       grind)
    | exact resolve eq44929 eq6575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6575 eq44929
  have eq45022 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44982 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44982
    | (have j0 := eq44982 X0 X1
       grind)
    | exact resolve eq44982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44982
  have eq46507 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43946 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43946
  have eq52814 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45022 x y
       grind)
    | exact superpose eq45022 eq16
    | (have j1 := eq45022 x y
       grind)
    | exact resolve eq16 eq45022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45022
  have eq53401 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52814
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq52814
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq52814 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52814
  have eq53407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq53401
  have eq53408 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq53407
  have eq53937 : (τ y) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq46507 y x
       have i₂ := eq53408
       grind)
    | exact superpose eq53408 eq46507
    | (have j0 := eq46507 y x
       grind)
    | exact resolve eq46507 eq53408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46507
  have eq53938 : (τ y) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq53937
  have eq53939 : y = (M.op x x) ∨ (τ (k y x)) = (τ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq53938
  have eq54441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k y x)) = (τ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7225 x
       have i₂ := eq53939
       grind)
    | exact superpose eq53939 eq7225
    | exact resolve eq7225 eq53939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53939
  have eq54473 : (σ y) = (σ (M.op x x)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have r₁ := eq54441
       have r₂ := eq16
       grind)
    | exact resolve eq54441 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54441
  have eq54503 : (M.op x x) = (τ (σ y)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq54473
       grind)
    | exact superpose eq54473 eq10
    | exact resolve eq10 eq54473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54473
  have eq54656 : y = (M.op x x) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq54503
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq54503
    | exact resolve eq54503 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54503
  have eq55246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq7225 x
       have i₂ := eq54656
       grind)
    | exact superpose eq54656 eq7225
    | exact resolve eq7225 eq54656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54656
  have eq55278 : (τ (k y x)) = (τ y) := by
    first
    | (have r₁ := eq55246
       have r₂ := eq16
       grind)
    | exact resolve eq55246 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55246
  have eq55304 : (k y x) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq55278
       grind)
    | exact superpose eq55278 eq11
    | exact resolve eq11 eq55278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55278
  have eq55499 : y = (k y x) := by
    first
    | (have i₁ := eq55304
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq55304
    | exact resolve eq55304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55304
  have eq56047 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq32826 y x
       have i₂ := eq55499
       grind)
    | exact superpose eq55499 eq32826
    | (have j0 := eq32826 y x
       grind)
    | exact resolve eq32826 eq55499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32826 eq55499
  have eq56050 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq56047
  have eq62970 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56050
       grind)
    | exact superpose eq56050 eq16
    | exact resolve eq16 eq56050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56050
  have eq63050 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq62970
       have i₂ := eq53408
       grind)
    | exact superpose eq53408 eq62970
    | exact resolve eq62970 eq53408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53408 eq62970
  have eq63051 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq63050
  have eq63052 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq63051
  have eq63652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7225 x
       have i₂ := eq63052
       grind)
    | exact superpose eq63052 eq7225
    | exact resolve eq7225 eq63052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63052
  have eq63685 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq63652
       have r₂ := eq16
       grind)
    | exact resolve eq63652 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63652
  have eq63716 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq63685
       grind)
    | exact superpose eq63685 eq10
    | exact resolve eq10 eq63685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63685
  have eq63886 : y = (M.op x x) := by
    first
    | (have i₁ := eq63716
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq63716
    | exact resolve eq63716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63716
  have eq64293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7225 x
       have i₂ := eq63886
       grind)
    | exact superpose eq63886 eq7225
    | exact resolve eq7225 eq63886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7225 eq63886
  have eq64327 : False := by grind
  exact eq64327

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | (have j0 := eq92 X1 X1
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq283 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq264
    | (have j0 := eq264 X0 X1
       grind)
    | exact resolve eq264 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq289 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq283 X0 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq283 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq283
  have eq293 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq289
    | (have j0 := eq289 X0 X1
       grind)
    | exact resolve eq289 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq289
  have eq382 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq293
    | exact resolve eq293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq293 (σ X1) X0
       grind)
    | exact superpose eq293 eq15
    | (have j1 := eq293 (σ X1) X0
       grind)
    | exact resolve eq15 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq404 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq393
    | (have j0 := eq393 X0 X1
       grind)
    | exact resolve eq393 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq426 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1
       have i₂ := eq382 X0 (τ X1)
       grind)
    | (have i₁ := eq102 X0
       have i₂ := eq382 (τ X0) (τ X0)
       grind)
    | exact superpose eq382 eq102
    | (have j1 := eq382 X0 (τ X1)
       grind)
    | exact resolve eq102 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq431 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq382 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq382 X0 X1
       grind)
    | exact superpose eq382 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq382 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq382 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq382 X0 X1
       grind)
    | exact resolve eq13 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq439 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq431 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq441 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq439 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq439 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq439 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq443 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq441 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq441
    | exact resolve eq441 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq441 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq479 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq443 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq443
    | (have j0 := eq443 X0 X1
       grind)
    | exact resolve eq443 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq1209 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq426 X0 X1
       grind)
    | exact superpose eq426 eq17
    | (have j1 := eq426 X0 X1
       grind)
    | exact resolve eq17 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq426
  have eq3201 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq479 y x
       grind)
    | exact superpose eq479 eq16
    | (have j1 := eq479 y x
       grind)
    | exact resolve eq16 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq3611 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1209 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1209
    | exact resolve eq1209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq3699 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3611 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3611
    | (have j0 := eq3611 X0 X1
       grind)
    | exact resolve eq3611 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611
  have eq3702 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3699 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq3699
    | (have j0 := eq3699 X0 X1
       grind)
    | exact resolve eq3699 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq3699
  have eq3703 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3702 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3702
    | (have j0 := eq3702 X0 X1
       grind)
    | exact resolve eq3702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3702
  have eq3718 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3201
       have i₂ := eq3703 y x
       grind)
    | exact superpose eq3703 eq3201
    | (have j1 := eq3703 y x
       grind)
    | (have r₁ := eq3201
       have r₂ := eq3703 y x
       grind)
    | exact resolve eq3201 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq3754 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq3718
  have eq6873 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq404 x y
       grind)
    | exact superpose eq404 eq16
    | (have j1 := eq404 x y
       grind)
    | exact resolve eq16 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq6980 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq6873
       have i₂ := eq3703 y x
       grind)
    | exact superpose eq3703 eq6873
    | (have j1 := eq3703 y x
       grind)
    | (have r₁ := eq6873
       have r₂ := eq3703 y x
       grind)
    | exact resolve eq6873 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703
  have eq6983 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq6980
  have eq7179 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6983
       grind)
    | exact superpose eq6983 eq16
    | exact resolve eq16 eq6983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6983
  have eq7214 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq7179
       have r₂ := eq3754
       grind)
    | exact resolve eq7179 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754 eq7179
  have eq7355 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq465 y x
       have i₂ := eq7214
       grind)
    | exact superpose eq7214 eq465
    | (have r₁ := eq465 y x
       have r₂ := eq7214
       grind)
    | exact resolve eq465 eq7214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq7530 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq7355 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7355
  have eq7666 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6873
       have i₂ := eq7530
       grind)
    | exact superpose eq7530 eq6873
    | exact resolve eq6873 eq7530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6873 eq7530
  have eq7674 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq7666
  have eq7675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7674
       have i₂ := eq7214
       grind)
    | exact superpose eq7214 eq7674
    | exact resolve eq7674 eq7214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214 eq7674
  have eq7676 : False := by grind
  exact eq7676

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X0))) X3 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq127 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq43 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq43
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq199 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100 x y
       grind)
    | exact superpose eq100 eq16
    | (have j1 := eq100 x y
       grind)
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) = (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42 (M.op X0 (M.op X1 (M.op X2 X0))) X3 X4 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq377 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq127 (M.op X0 (M.op X1 (M.op X2 X0))) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq127
    | exact resolve eq127 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (M.op (σ (k X0 X1)) (M.op (σ X0) (M.op X2 (M.op X3 (σ X0)))))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 (σ X1) (σ X0) X2 X3
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq127
    | (have j1 := eq100 X1 X0
       grind)
    | exact resolve eq127 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq885 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq932 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq1821 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq199
       have i₂ := eq932 x y
       grind)
    | exact superpose eq932 eq199
    | (have j1 := eq932 x y
       grind)
    | (have r₁ := eq199
       have r₂ := eq932 x y
       grind)
    | (have r₁ := eq199
       have r₂ := eq932 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq199
       have r₂ := eq932 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq199 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1822 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1821
  have eq7604 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op X5 X0) (M.op (M.op X5 X0) (M.op X0 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0))))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq127 X0 X5 (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0)))))) (M.op (M.op X0 (M.op X1 (M.op X2 X0))) (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X0))))))
       have i₂ := eq302 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq302 eq127
    | exact resolve eq127 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq302
  have eq20730 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1822
       grind)
    | exact superpose eq1822 eq16
    | exact resolve eq16 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822
  have eq20731 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20730
       have r₂ := eq22 x
       grind)
    | exact resolve eq20730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20730
  have eq21017 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq60 y (σ x)
       have i₂ := eq20731
       grind)
    | exact superpose eq20731 eq60
    | (have j0 := eq60 y (σ x)
       grind)
    | (have r₁ := eq60 y (σ x)
       have r₂ := eq20731
       grind)
    | exact resolve eq60 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20731
  have eq21046 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21017
  have eq21047 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21046
  have eq21052 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq21047
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21047
    | exact resolve eq21047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21047
  have eq21054 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (k y X0) ∨ y = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq21052
       grind)
    | exact superpose eq21052 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21052
       grind)
    | exact resolve eq13 eq21052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21052
  have eq72286 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j0 := eq21054 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21054
  have eq72819 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72286
       grind)
    | exact superpose eq72286 eq16
    | exact resolve eq16 eq72286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72286
  have eq72820 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq72819
       have r₂ := eq22 x
       grind)
    | exact resolve eq72819 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72819
  have eq72821 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72820
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq72820
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq72820 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72826 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq203 x y
       have i₂ := eq72820
       grind)
    | exact superpose eq72820 eq203
    | (have j0 := eq203 x y
       grind)
    | exact resolve eq203 eq72820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72902 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq72826
  have eq98764 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72821
       grind)
    | exact superpose eq72821 eq16
    | exact resolve eq16 eq72821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72821
  have eq98765 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq98764
       have r₂ := eq22 x
       grind)
    | exact resolve eq98764 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98764
  have eq98797 : ∀ X0 X1 X2 X3 : G, y = (M.op y (M.op y (M.op y (M.op (M.op y (M.op X0 (M.op X1 y))) (M.op X2 (M.op X3 (M.op y (M.op X0 (M.op X1 y))))))))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7604 y X1 X2 X3 x x
       have i₂ := eq98765
       grind)
    | exact superpose eq98765 eq7604
    | exact resolve eq7604 eq98765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98809 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98797 x x x x
       have i₂ := eq377 y x x x x
       grind)
    | exact superpose eq377 eq98797
    | exact resolve eq98797 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98797
  have eq99129 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq98809
  have eq99132 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq99129
       have r₂ := eq98765
       grind)
    | exact resolve eq99129 eq98765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98765 eq99129
  have eq99142 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (k y X0) ∨ y = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq99132
       grind)
    | exact superpose eq99132 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq99132
       grind)
    | exact resolve eq13 eq99132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104526 : x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq99142 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99142
  have eq104527 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq104526
       grind)
    | exact superpose eq104526 eq16
    | exact resolve eq16 eq104526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104526
  have eq104528 : y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq104527
       have r₂ := eq22 x
       grind)
    | exact resolve eq104527 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104527
  have eq105155 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq203 x y
       have i₂ := eq104528
       grind)
    | exact superpose eq104528 eq203
    | (have j0 := eq203 x y
       grind)
    | exact resolve eq203 eq104528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq105260 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq105155
  have eq109867 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq382 y x x x
       have i₂ := eq104528
       grind)
    | exact superpose eq104528 eq382
    | (have j0 := eq382 y x x x
       grind)
    | exact resolve eq382 eq104528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104528
  have eq109868 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 y x x x
       have i₂ := eq72820
       grind)
    | exact superpose eq72820 eq382
    | (have j0 := eq382 y x x x
       grind)
    | exact resolve eq382 eq72820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq72820
  have eq110111 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    intro X0 X1
    first
    | (have j0 := eq109868 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109868
  have eq110112 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq109867 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109867
  have eq110221 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq110111 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq110111
    | exact resolve eq110111 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110111
  have eq110222 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq110112 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq110112
    | exact resolve eq110112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110112
  have eq110332 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq110221
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq110221
    | exact resolve eq110221 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110221
  have eq110333 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq110222
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq110222
    | exact resolve eq110222 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110222
  have eq110408 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq110332
       have r₂ := eq72902
       grind)
    | exact resolve eq110332 eq72902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72902 eq110332
  have eq110409 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq110333
       have r₂ := eq105260
       grind)
    | exact resolve eq110333 eq105260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105260 eq110333
  have eq110628 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq60 y (σ x)
       have i₂ := eq110408
       grind)
    | exact superpose eq110408 eq60
    | (have j0 := eq60 y (σ x)
       grind)
    | (have r₁ := eq60 y (σ x)
       have r₂ := eq110408
       grind)
    | exact resolve eq60 eq110408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq110408
  have eq110683 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq110628
  have eq110684 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq110683
  have eq110693 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq110684
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq110684
    | exact resolve eq110684 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110684
  have eq110694 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq110693
  have eq110697 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq110694
       grind)
    | exact superpose eq110694 eq10
    | exact resolve eq10 eq110694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110694
  have eq110928 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq110697
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq110697
    | exact resolve eq110697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110697
  have eq111738 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110928
       grind)
    | exact superpose eq110928 eq16
    | exact resolve eq16 eq110928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110928
  have eq111739 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq111738
       have r₂ := eq22 x
       grind)
    | exact resolve eq111738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111738
  have eq111747 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq199
       have i₂ := eq111739
       grind)
    | exact superpose eq111739 eq199
    | exact resolve eq199 eq111739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq111739
  have eq112007 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq111747
       have r₂ := eq110409
       grind)
    | exact resolve eq111747 eq110409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110409 eq111747
  have eq117436 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq112007
       grind)
    | exact superpose eq112007 eq16
    | exact resolve eq16 eq112007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112007
  have eq117512 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117436
       have i₂ := eq99132
       grind)
    | exact superpose eq99132 eq117436
    | exact resolve eq117436 eq99132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99132
  have eq117518 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq117512
  have eq117519 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq117518
  have eq118239 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq117519
       grind)
    | exact superpose eq117519 eq10
    | exact resolve eq10 eq117519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118479 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq118239
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq118239
    | exact resolve eq118239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118239
  have eq118515 : ∀ X0 X1 X2 X3 : G, y = (M.op y (M.op y (M.op y (M.op (M.op y (M.op X0 (M.op X1 y))) (M.op X2 (M.op X3 (M.op y (M.op X0 (M.op X1 y))))))))) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7604 y X1 X2 X3 x x
       have i₂ := eq118479
       grind)
    | exact superpose eq118479 eq7604
    | exact resolve eq7604 eq118479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7604 eq118479
  have eq118533 : y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq118515 x x x x
       have i₂ := eq377 y x x x x
       grind)
    | exact superpose eq377 eq118515
    | exact resolve eq118515 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq118515
  have eq119408 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117436
       have i₂ := eq118533
       grind)
    | exact superpose eq118533 eq117436
    | exact resolve eq117436 eq118533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117436 eq118533
  have eq119491 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq119408
  have eq119503 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq119491
       have r₂ := eq117519
       grind)
    | exact resolve eq119491 eq117519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117519 eq119491
  have eq119508 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq119503
       grind)
    | exact superpose eq119503 eq16
    | exact resolve eq16 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119509 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq119503
       grind)
    | exact superpose eq119503 eq10
    | exact resolve eq10 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119503
  have eq119751 : x = y := by
    first
    | (have i₁ := eq119509
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq119509
    | exact resolve eq119509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119509
  have eq119752 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq119508
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq119508
    | exact resolve eq119508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq119508
  have eq119753 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq119752
       have i₂ := eq119751
       grind)
    | exact superpose eq119751 eq119752
    | exact resolve eq119752 eq119751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119751 eq119752
  have eq119754 : False := by grind
  exact eq119754

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq106 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  clear eq19
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq117 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq505 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq702 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq16
    | (have j1 := eq115 x y
       grind)
    | exact resolve eq16 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq722 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq771 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq828 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq711
    | (have j0 := eq711 (τ X0) (τ X1)
       grind)
    | exact resolve eq711 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq711
  have eq836 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq839 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq836
    | (have j0 := eq836 X0 X1
       grind)
    | exact resolve eq836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq841 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq839
    | (have j0 := eq839 X0 X1
       grind)
    | exact resolve eq839 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq842 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq841
    | (have j0 := eq841 X0 X1
       grind)
    | exact resolve eq841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq843 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq842
    | (have j0 := eq842 X0 X1
       grind)
    | exact resolve eq842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq844 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq843
    | (have j0 := eq843 X0 X1
       grind)
    | exact resolve eq843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq3661 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq114 X1 X0
       grind)
    | exact superpose eq114 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq114 X1 X0
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq114 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq114 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq13 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq3665 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3661 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3666 : ∀ X0 X1 : G, (τ X0) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3665 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3665
  have eq3668 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3666 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq3666
    | (have j0 := eq3666 X0 X1
       grind)
    | exact resolve eq3666 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq3666
  have eq6422 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq702
       have i₂ := eq771 x y
       grind)
    | exact superpose eq771 eq702
    | (have j1 := eq771 (σ x) (σ y)
       grind)
    | (have r₁ := eq702
       have r₂ := eq771 x y
       grind)
    | (have r₁ := eq702
       have r₂ := eq771 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq702
       have r₂ := eq771 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq702 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq6423 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6422
  have eq6827 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6423
       grind)
    | exact superpose eq6423 eq16
    | exact resolve eq16 eq6423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423
  have eq6828 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6827
       have r₂ := eq22 x
       grind)
    | exact resolve eq6827 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6827
  have eq6835 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op y (M.op X0 (M.op X1 y))))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq505 y x x x
       have i₂ := eq6828
       grind)
    | exact superpose eq6828 eq505
    | exact resolve eq505 eq6828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6828
  have eq6838 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6835 x x
       have i₂ := eq9 y x x
       grind)
    | exact superpose eq9 eq6835
    | exact resolve eq6835 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6835
  have eq6847 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq505 (σ y) (σ x) x x
       have i₂ := eq6838
       grind)
    | exact superpose eq6838 eq505
    | exact resolve eq505 eq6838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq6838
  have eq6852 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6847 x x
       have i₂ := eq9 (σ y) x x
       grind)
    | exact superpose eq9 eq6847
    | exact resolve eq6847 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6847
  have eq6855 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6852
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq6852
    | exact resolve eq6852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6852
  have eq6861 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6855
       grind)
    | exact superpose eq6855 eq10
    | exact resolve eq10 eq6855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6855
  have eq6912 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6861
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6861
    | exact resolve eq6861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6861
  have eq6914 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6912
       grind)
    | exact superpose eq6912 eq16
    | exact resolve eq16 eq6912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6912
  have eq6915 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq6914
       have r₂ := eq22 x
       grind)
    | exact resolve eq6914 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6914
  have eq6918 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq106 y X0
       have i₂ := eq6915
       grind)
    | exact superpose eq6915 eq106
    | exact resolve eq106 eq6915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq6915
  have eq7367 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (σ y) (σ y) x
       have i₂ := eq6918 x
       grind)
    | exact superpose eq6918 eq9
    | exact resolve eq9 eq6918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6918
  have eq7381 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq7367
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq7367
    | exact resolve eq7367 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7367
  have eq7382 : (σ y) = (σ (M.op y y)) := by grind
  clear eq7381
  have eq7396 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq7382
       grind)
    | exact superpose eq7382 eq10
    | exact resolve eq10 eq7382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7398 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op y y)
       have i₂ := eq7382
       grind)
    | exact superpose eq7382 eq15
    | exact resolve eq15 eq7382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7445 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq7398 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq7398
    | exact resolve eq7398 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7398
  have eq7447 : y = (M.op y y) := by
    first
    | (have i₁ := eq7396
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7396
    | exact resolve eq7396 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7396
  have eq26623 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3668 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3668
    | (have j0 := eq3668 (M.op (σ X0) (σ X0)) (k X1 X0)
       grind)
    | exact resolve eq3668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668
  have eq26728 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26623 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq26623
    | (have j0 := eq26623 X0 X1
       grind)
    | exact resolve eq26623 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26623
  have eq26735 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26728 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq26728
    | (have j0 := eq26728 X0 X1
       grind)
    | exact resolve eq26728 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26728
  have eq26739 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26735 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq26735
    | (have j0 := eq26735 X0 X1
       grind)
    | exact resolve eq26735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26735
  have eq26824 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 (M.op y y))) ∨ (M.op (M.op y y) (M.op y y)) = (k X0 (M.op y y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq7445 X0
       have i₂ := eq26739 (M.op y y) X0
       grind)
    | exact superpose eq26739 eq7445
    | (have j1 := eq26739 (M.op y y) X0
       grind)
    | exact resolve eq7445 eq26739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7445 eq26739
  have eq26933 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (M.op (M.op y y) (M.op y y)) = (k X0 (M.op y y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26824 X0
       have i₂ := eq7447
       grind)
    | exact superpose eq7447 eq26824
    | (have j0 := eq26824 X0
       grind)
    | exact resolve eq26824 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26824
  have eq26981 : ∀ X0 : G, (M.op y y) = (k X0 y) ∨ (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26933 X0
       have i₂ := eq7447
       grind)
    | exact superpose eq7447 eq26933
    | (have j0 := eq26933 X0
       grind)
    | exact resolve eq26933 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26933
  have eq27013 : ∀ X0 : G, y = (k X0 y) ∨ (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26981 X0
       have i₂ := eq7447
       grind)
    | exact superpose eq7447 eq26981
    | (have j0 := eq26981 X0
       grind)
    | exact resolve eq26981 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26981
  have eq27029 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ y = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq27013 X0
       have i₂ := eq7447
       grind)
    | exact superpose eq7447 eq27013
    | (have j0 := eq27013 X0
       grind)
    | exact resolve eq27013 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7447 eq27013
  have eq27594 : ∀ X0 : G, (k X0 y) = (τ (σ (M.op X0 y))) ∨ y = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 y)
       have i₂ := eq27029 X0
       grind)
    | exact superpose eq27029 eq10
    | (have j1 := eq27029 X0
       grind)
    | exact resolve eq10 eq27029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27029
  have eq27664 : ∀ X0 : G, y = (k X0 y) ∨ (M.op X0 y) = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq27594 X0
       have i₂ := eq10 (M.op X0 y)
       grind)
    | exact superpose eq10 eq27594
    | (have j0 := eq27594 X0
       grind)
    | exact resolve eq27594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27594
  have eq27778 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq27664 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27664
  have eq27817 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq27778 X0
       have j1 := eq14 X0 y
       grind)
    | (have r₁ := eq27778 X0
       have r₂ := eq14 X0 y
       grind)
    | (have r₁ := eq27778 X0
       have r₂ := eq14 y (M.op X0 y)
       grind)
    | (have r₁ := eq27778 X0
       have r₂ := eq14 (M.op X0 y) y
       grind)
    | exact resolve eq27778 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27778
  have eq27895 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq702
       have i₂ := eq27817 x
       grind)
    | exact superpose eq27817 eq702
    | (have j1 := eq27817 x
       grind)
    | exact resolve eq702 eq27817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq27817
  have eq27905 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27895
  have eq28710 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq27905
       grind)
    | exact superpose eq27905 eq16
    | exact resolve eq16 eq27905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28722 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq27905
       grind)
    | exact superpose eq27905 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq27905
       grind)
    | exact resolve eq13 eq27905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27905
  have eq28736 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq28722
  have eq28737 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq28736
  have eq28747 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28737
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq28737
    | exact resolve eq28737 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28737
  have eq28762 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28747
       have i₂ := eq7382
       grind)
    | exact superpose eq7382 eq28747
    | exact resolve eq28747 eq7382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7382 eq28747
  have eq28766 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq28762
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq28762
    | exact resolve eq28762 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28762
  have eq29189 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28766
       grind)
    | exact superpose eq28766 eq10
    | exact resolve eq10 eq28766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28766
  have eq29264 : x = y ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq29189
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29189
    | exact resolve eq29189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29189
  have eq29265 : (σ y) = (σ (k x y)) ∨ x = y := by grind
  clear eq29264
  have eq29295 : (k x y) = (τ (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq29265
       grind)
    | exact superpose eq29265 eq10
    | exact resolve eq10 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29265
  have eq29378 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq29295
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29295
    | exact resolve eq29295 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29295
  have eq29410 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq844 x y
       have i₂ := eq29378
       grind)
    | exact superpose eq29378 eq844
    | (have j0 := eq844 x y
       grind)
    | (have r₁ := eq844 x y
       have r₂ := eq29378
       grind)
    | exact resolve eq844 eq29378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq29378
  have eq29446 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq29410
  have eq29447 : y = (M.op x y) ∨ x = y := by grind
  clear eq29446
  have eq29469 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq28710
       have i₂ := eq29447
       grind)
    | exact superpose eq29447 eq28710
    | exact resolve eq28710 eq29447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28710 eq29447
  have eq29516 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29469
  have eq29517 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq29516
  have eq29550 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29517
       grind)
    | exact superpose eq29517 eq10
    | exact resolve eq10 eq29517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29517
  have eq29625 : x = y ∨ x = y := by
    first
    | (have i₁ := eq29550
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29550
    | exact resolve eq29550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29550
  have eq29626 : x = y := by grind
  clear eq29625
  have eq29633 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29626
       grind)
    | exact superpose eq29626 eq16
    | exact resolve eq16 eq29626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29626
  have eq29724 : False := by grind
  exact eq29724

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq266 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq269 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq267 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq280 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq269 (σ X0)
       grind)
    | exact superpose eq269 eq15
    | exact resolve eq15 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq269 (τ X0)
       grind)
    | exact superpose eq269 eq31
    | exact resolve eq31 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq293 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq286
    | exact resolve eq286 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq299 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq269 X0
       grind)
    | exact superpose eq269 eq280
    | exact resolve eq280 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq280
  have eq342 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq346 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq343 X0 X1
       grind)
    | (have r₁ := eq342 X0 X1
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq342 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq343
  have eq357 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq293 X0
       grind)
    | exact superpose eq293 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq361 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       have j1 := eq358 X0 X1
       grind)
    | (have r₁ := eq357 X0 X1
       have r₂ := eq358 X0 X1
       grind)
    | exact resolve eq357 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq358
  have eq380 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq346
    | exact resolve eq346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq346 y (σ x)
       grind)
    | exact superpose eq346 eq16
    | (have j1 := eq346 y (σ x)
       grind)
    | exact resolve eq16 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq346 X1 X0
       grind)
    | exact superpose eq346 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq346 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq13 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq391 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq393 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq391 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq391 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq395 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq384
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq384
    | exact resolve eq384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq405 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq380 X1 X0
       grind)
    | exact superpose eq380 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq380 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq380 X0 X1
       grind)
    | exact resolve eq13 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq410 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq412 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq410 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq410 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq410 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq428 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq412 X0 (τ X1)
       grind)
    | exact superpose eq412 eq18
    | (have j1 := eq412 X0 (τ X1)
       grind)
    | exact resolve eq18 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq445 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq412 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq428 (τ X0) X1
       grind)
    | exact superpose eq428 eq17
    | (have j1 := eq428 (τ X0) X1
       grind)
    | exact resolve eq17 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq428
  have eq1027 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1020
    | (have j0 := eq1020 X0 X1
       grind)
    | exact resolve eq1020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1038 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1027 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1027
    | (have j0 := eq1027 X0 X1
       grind)
    | exact resolve eq1027 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1039 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1038 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1038
    | (have j0 := eq1038 X0 X1
       grind)
    | exact resolve eq1038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1095 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X0 X1
       have i₂ := eq412 X0 X1
       grind)
    | exact superpose eq412 eq1039
    | (have j0 := eq1039 X0 X1
       have j1 := eq412 X0 X1
       grind)
    | exact resolve eq1039 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq1096 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ (σ X1)))) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X0 (σ X1)
       have i₂ := eq393 X0 X1
       grind)
    | exact superpose eq393 eq1039
    | (have j0 := eq1039 X0 (σ X1)
       have j1 := eq393 X0 X1
       grind)
    | exact resolve eq1039 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq1039
  have eq1157 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) (τ (σ X1)))) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1096 X0 X1
       have j1 := eq445 X0 (σ X1)
       grind)
    | (have r₁ := eq1096 X0 X1
       have r₂ := eq445 X0 (σ X1)
       grind)
    | exact resolve eq1096 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1158 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1095 X0 X1
       have j1 := eq445 X0 X1
       grind)
    | (have r₁ := eq1095 X0 X1
       have r₂ := eq445 X0 X1
       grind)
    | exact resolve eq1095 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq1095
  have eq1178 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1157 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1157
    | (have j0 := eq1157 X0 X1
       grind)
    | exact resolve eq1157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1208 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq1158 (σ X0) X1
       grind)
    | exact superpose eq1158 eq28
    | (have j1 := eq1158 (σ X0) X1
       grind)
    | exact resolve eq28 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1228 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1208
    | (have j0 := eq1208 X0 X1
       grind)
    | exact resolve eq1208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1254 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1228 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1228
    | (have j0 := eq1228 X0 X1
       grind)
    | exact resolve eq1228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1779 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1178 (σ X0) X1
       grind)
    | exact superpose eq1178 eq28
    | (have j1 := eq1178 (σ X0) X1
       grind)
    | exact resolve eq28 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1178
  have eq1790 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1779 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1779
    | (have j0 := eq1779 X0 X1
       grind)
    | exact resolve eq1779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1805 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1790 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1790
    | (have j0 := eq1790 X0 X1
       grind)
    | exact resolve eq1790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1814 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1805 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1805
    | (have j0 := eq1805 X0 X1
       grind)
    | exact resolve eq1805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq1837 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1814 x y
       grind)
    | exact superpose eq1814 eq16
    | (have j1 := eq1814 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1814 x y
       grind)
    | exact resolve eq16 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1863 : x = (k x y) := by grind
  clear eq1837
  have eq1908 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X1 X0
       have i₂ := eq1254 X0 X1
       grind)
    | exact superpose eq1254 eq361
    | (have j0 := eq361 X1 X0
       have j1 := eq1254 X0 X1
       grind)
    | exact resolve eq361 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq1254
  have eq1921 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq2051 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1921 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1921
    | exact resolve eq1921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq2168 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2051 y x
       grind)
    | exact superpose eq2051 eq16
    | (have j1 := eq2051 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq2051 y x
       grind)
    | exact resolve eq16 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051
  have eq2194 : x = (M.op x y) := by grind
  clear eq2168
  have eq2223 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq395
       have i₂ := eq2194
       grind)
    | exact superpose eq2194 eq395
    | exact resolve eq395 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq2230 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq2223
  have eq2234 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq1863
       grind)
    | exact superpose eq1863 eq2230
    | exact resolve eq2230 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863 eq2230
  have eq2240 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2234
       grind)
    | exact superpose eq2234 eq16
    | exact resolve eq16 eq2234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234
  have eq2254 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2240
       have i₂ := eq2194
       grind)
    | exact superpose eq2194 eq2240
    | exact resolve eq2240 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194 eq2240
  have eq2255 : False := by grind
  exact eq2255

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq115 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq600 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq115 X1 X0
       grind)
    | exact superpose eq115 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq115 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq115 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq115 X0 (M.op X0 (τ X0))
       grind)
    | exact resolve eq13 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq601 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq600 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq602 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq601 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq779 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2104 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq602
    | exact resolve eq602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq2153 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2104 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2104
    | (have j0 := eq2104 X0 X1
       grind)
    | exact resolve eq2104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104
  have eq2192 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2153 X0 X1
       grind)
    | exact superpose eq2153 eq10
    | (have j1 := eq2153 X0 X1
       grind)
    | exact resolve eq10 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2234 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2192 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2192
    | (have j0 := eq2192 X0 X1
       grind)
    | exact resolve eq2192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192
  have eq2272 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq2234 (σ X0) X1
       grind)
    | exact superpose eq2234 eq37
    | (have j1 := eq2234 (σ X0) X1
       grind)
    | exact resolve eq37 eq2234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2234
  have eq3923 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2272 X1 (σ X0)
       grind)
    | exact superpose eq2272 eq28
    | (have j1 := eq2272 X1 (σ X0)
       grind)
    | exact resolve eq28 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2272
  have eq3984 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3923 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3923
    | (have j0 := eq3923 X0 X1
       grind)
    | exact resolve eq3923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq4018 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3984 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3984
    | (have j0 := eq3984 X0 X1
       grind)
    | exact resolve eq3984 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984
  have eq4028 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4018 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4018
    | (have j0 := eq4018 X0 X1
       grind)
    | exact resolve eq4018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4018
  have eq4255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4028 X1 X0
       grind)
    | exact superpose eq4028 eq11
    | (have j1 := eq4028 X1 X0
       grind)
    | exact resolve eq11 eq4028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq5117 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4255 x y
       grind)
    | exact superpose eq4255 eq16
    | (have j1 := eq4255 x y
       grind)
    | exact resolve eq16 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255
  have eq5143 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5117
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5117
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5117
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5117
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5117 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5117
       have i₂ := eq2153 x y
       grind)
    | exact superpose eq2153 eq5117
    | (have j1 := eq2153 x y
       grind)
    | (have r₁ := eq5117
       have r₂ := eq2153 x y
       grind)
    | (have r₁ := eq5117
       have r₂ := eq2153 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5117
       have r₂ := eq2153 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5117 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq5117
  have eq5147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5144
  have eq5148 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq5147
  have eq5149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5143
  have eq5150 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5149
  have eq5154 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5148
       grind)
    | exact superpose eq5148 eq16
    | exact resolve eq16 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5148
  have eq5155 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5154
       have r₂ := eq22 x
       grind)
    | exact resolve eq5154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq5161 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq779 x y
       have i₂ := eq5155
       grind)
    | exact superpose eq5155 eq779
    | (have j0 := eq779 x y
       grind)
    | exact resolve eq779 eq5155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq5155
  have eq5166 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5161
  have eq5167 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5166
  have eq5179 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5167
       grind)
    | exact superpose eq5167 eq16
    | exact resolve eq16 eq5167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5167
  have eq5196 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5179
       have i₂ := eq5150
       grind)
    | exact superpose eq5150 eq5179
    | exact resolve eq5179 eq5150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5150 eq5179
  have eq5197 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5196
  have eq5198 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5197
  have eq5199 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5198
       grind)
    | exact superpose eq5198 eq16
    | exact resolve eq16 eq5198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5198
  have eq5200 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5199
       have r₂ := eq22 x
       grind)
    | exact resolve eq5199 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199
  have eq5201 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5200
       grind)
    | exact superpose eq5200 eq16
    | exact resolve eq16 eq5200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5202 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5200
       grind)
    | exact superpose eq5200 eq10
    | exact resolve eq10 eq5200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5200
  have eq5254 : x = y := by
    first
    | (have i₁ := eq5202
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5202
    | exact resolve eq5202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5202
  have eq5255 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5201
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5201
    | exact resolve eq5201 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5201
  have eq5256 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5255
       have i₂ := eq5254
       grind)
    | exact superpose eq5254 eq5255
    | exact resolve eq5255 eq5254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5254 eq5255
  have eq5257 : False := by grind
  exact eq5257

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq32
    | exact resolve eq32 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32
  have eq67 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq17
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq71 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq71 (τ X0) X1
       grind)
    | exact superpose eq71 eq17
    | exact resolve eq17 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq84 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq91 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq84 (τ X0) X1
       grind)
    | exact superpose eq84 eq17
    | exact resolve eq17 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq92 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq135 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq74
    | (have j0 := eq74 X2 X2
       grind)
    | exact resolve eq74 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq238 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq92 (τ X0) X1
       grind)
    | exact superpose eq92 eq17
    | exact resolve eq17 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq240 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq238
    | exact resolve eq238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq308 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq240 (τ X0) X1
       grind)
    | exact superpose eq240 eq17
    | exact resolve eq17 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq312 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq308
    | exact resolve eq308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq391 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))
       have i₂ := eq312 (τ X0) X1
       grind)
    | exact superpose eq312 eq17
    | exact resolve eq17 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq395 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq391
    | exact resolve eq391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq2395 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X0) (k X1 (σ X2))
       have i₂ := eq135 X1 X2 X0
       grind)
    | exact superpose eq135 eq19
    | (have j1 := eq135 X1 X2 X0
       grind)
    | exact resolve eq19 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq135
  have eq2396 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2395 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq17099 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X1) X2) (τ X0))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2396 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2396
    | exact resolve eq2396 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq17193 : ∀ X0 X1 X2 : G, (k (σ (k (τ X1) X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17099 X0 X1 X2
       have i₂ := eq18 X0 (k (τ X1) X2)
       grind)
    | exact superpose eq18 eq17099
    | (have j0 := eq17099 X0 X1 X2
       grind)
    | exact resolve eq17099 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17099
  have eq17208 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17193 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq17193
    | (have j0 := eq17193 X0 X1 X2
       grind)
    | exact resolve eq17193 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq17193
  have eq17209 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) X0) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17208 X0 X1 X2
       have j1 := eq12 (k X1 (σ X2)) X0
       grind)
    | (have r₁ := eq17208 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq17208 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17208
  have eq17239 : ∀ X0 X2 : G, (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq17209 X0 X0 (σ (σ (σ (σ (σ (M.op x x))))))
       have i₂ := eq395 X0 x
       grind)
    | exact superpose eq395 eq17209
    | exact resolve eq17209 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq17209
  have eq17742 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq17239 (σ X0) (σ X1)
       grind)
    | exact superpose eq17239 eq15
    | exact resolve eq15 eq17239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17824 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17742 X0 X1
       have i₂ := eq17239 X0 X1
       grind)
    | exact superpose eq17239 eq17742
    | exact resolve eq17742 eq17239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17239 eq17742
  have eq20204 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17824 x y
       grind)
    | exact superpose eq17824 eq16
    | (have r₁ := eq16
       have r₂ := eq17824 x y
       grind)
    | exact resolve eq16 eq17824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17824
  have eq20274 : False := by grind
  exact eq20274

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq2662 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2766 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2662 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2767 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2766 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq4183 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2767 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767
  have eq4206 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4183 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq4183 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq4183 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq4183 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq4183 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183
  have eq4353 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4206 X0 (τ X1)
       grind)
    | exact superpose eq4206 eq19
    | (have j1 := eq4206 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq4206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4364 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4206 (σ X0) (σ X1)
       grind)
    | exact superpose eq4206 eq15
    | (have j1 := eq4206 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4206
  have eq4487 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4353 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4353
    | exact resolve eq4353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4353
  have eq4548 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4487 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4487
    | (have j0 := eq4487 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq4487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487
  have eq4869 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4364 x y
       grind)
    | exact superpose eq4364 eq16
    | (have j1 := eq4364 x y
       grind)
    | exact resolve eq16 eq4364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364
  have eq4911 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4869
       have i₂ := eq4548 y x
       grind)
    | exact superpose eq4548 eq4869
    | (have j1 := eq4548 (σ x) (σ y)
       grind)
    | (have r₁ := eq4869
       have r₂ := eq4548 y x
       grind)
    | (have r₁ := eq4869
       have r₂ := eq4548 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4869
       have r₂ := eq4548 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4869 eq4548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4548 eq4869
  have eq4912 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq4911
  have eq4916 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4912
       grind)
    | exact superpose eq4912 eq10
    | exact resolve eq10 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4912
  have eq4957 : x = y ∨ x = y := by
    first
    | (have i₁ := eq4916
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4916
    | exact resolve eq4916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916
  have eq4958 : x = y := by grind
  clear eq4957
  have eq4960 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4958
       grind)
    | exact superpose eq4958 eq16
    | exact resolve eq16 eq4958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4958
  have eq4961 : False := by grind
  exact eq4961
