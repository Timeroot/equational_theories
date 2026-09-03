import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3296`: `x ◇ x = y ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step. -/
theorem DiagFix_Equation3296 : AutBox.DiagFix Law3296 := by
  classical
  refine AutBox.diagFix_of (fun {G} _ M hM σ hbij hoff x ↦ ?_)
  have hm := (@Law3296.models_iff G M).mp hM
  obtain ⟨τ, hi1, hi2⟩ := Function.bijective_iff_has_inverse.mp hbij
  have hd : ∀ a b : G, a = b ∨ σ (M.op a b) = M.op (σ a) (σ b) :=
    fun a b ↦ (eq_or_ne a b).imp id (hoff a b)
  by_contra nh
  have eq6 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2
    grind
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq8 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq10 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by grind
  clear hm hd nh hM hoff hbij hi1 hi2
  have eq11 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6 X2 X3 X4
       have i₂ := eq6 X2 X0 X1
       grind)
    | exact superpose eq6 eq6
    | exact resolve eq6 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 (M.op X1 (M.op X1 X0)) X2 X3
       have i₂ := eq6 X0 X3 X1
       grind)
    | exact superpose eq6 eq6
    | exact resolve eq6 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 (M.op X1 X0) X2 X1
       have i₂ := eq6 X0 X1 X1
       grind)
    | exact superpose eq6 eq6
    | exact resolve eq6 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X0 x X2 X3
       have i₂ := eq6 X0 (M.op x (M.op x X0)) x
       grind)
    | (have i₁ := eq14 X0 x X2 X3
       have i₂ := eq6 (M.op x (M.op x X0)) x X2
       grind)
    | exact superpose eq6 eq14
    | exact resolve eq14 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14
  have eq18 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17 X0 X2 X3
       have i₂ := eq6 X0 X1 X2
       grind)
    | exact superpose eq6 eq17
    | exact resolve eq17 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq9
    | (have j0 := eq9 (σ (M.op (τ X0) X1)) (M.op X0 (σ X1))
       grind)
    | exact resolve eq9 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (M.op (σ X0) (σ (M.op X0 X1)))) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 (σ X1) X2 (σ X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq6
    | (have j1 := eq9 (M.op (σ X1) (σ X1)) (M.op X2 (M.op (σ X0) (σ (M.op X0 X1))))
       grind)
    | exact resolve eq6 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X1 X2))) (M.op X0 (M.op X1 (M.op X1 X2)))) = (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 X0 X0 X2
       have i₂ := eq6 X0 X1 X2
       grind)
    | exact superpose eq6 eq15
    | exact resolve eq15 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq15 X1 x X3
       have i₂ := eq15 X1 x X0
       grind)
    | (have i₁ := eq15 X0 X0 x
       have i₂ := eq15 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq15
    | exact resolve eq15 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq15 (M.op X3 X1) X2 X4
       have i₂ := eq15 X1 X3 X0
       grind)
    | (have i₁ := eq15 (M.op X0 X0) X1 X2
       have i₂ := eq15 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq15
    | exact resolve eq15 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0 x
       have i₂ := eq15 X1 X2 x
       grind)
    | (have i₁ := eq15 X0 X1 (M.op X0 X0)
       have i₂ := eq15 X0 X0 X2
       grind)
    | exact superpose eq15 eq15
    | exact resolve eq15 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X4 (M.op X4 (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6 (M.op X2 X1) X3 X4
       have i₂ := eq15 X1 X2 X0
       grind)
    | (have i₁ := eq6 (M.op X0 X0) X1 X2
       have i₂ := eq15 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq6
    | exact resolve eq6 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X1 X2 x
       have i₂ := eq15 X1 X0 x
       grind)
    | (have i₁ := eq17 X0 X2 (M.op X0 X0)
       have i₂ := eq15 X0 X0 X2
       grind)
    | exact superpose eq15 eq17
    | exact resolve eq17 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq49 x X1 X2 X3 x
       have i₂ := eq17 X1 x x
       grind)
    | (have i₁ := eq49 x X1 X2 X3 (M.op x (M.op X1 X1))
       have i₂ := eq17 (M.op x (M.op X1 X1)) X2 X3
       grind)
    | exact superpose eq17 eq49
    | exact resolve eq49 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq77 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X2 (M.op X2 X0)))) ∨ (M.op X2 (M.op X2 X0)) = (τ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op X2 (M.op X2 X0))
       have i₂ := eq6 X0 (τ X1) X2
       grind)
    | exact superpose eq6 eq31
    | (have j0 := eq31 X1 (M.op X2 (M.op X2 X0))
       grind)
    | exact resolve eq31 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X0 (M.op X1 (M.op X1 X2)))) = (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40 X0 X0 X3
       have i₂ := eq6 X0 X1 X2
       grind)
    | exact superpose eq6 eq40
    | exact resolve eq40 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op (M.op X2 X0) (M.op X2 X0)))) ∨ (τ X1) = (M.op (M.op X2 X0) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X0) (M.op X2 X0))
       have i₂ := eq62 X2 X0 (τ X1)
       grind)
    | exact superpose eq62 eq31
    | (have j0 := eq31 X1 (M.op (M.op X2 X0) (M.op X2 X0))
       grind)
    | exact resolve eq31 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (M.op X0 (σ (M.op (τ X0) X1)))) ∨ (τ X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (τ X0) X1 X2
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq33
    | (have j0 := eq33 (M.op (σ X1) (σ X1)) (M.op X2 (M.op X0 (σ (M.op (τ X0) X1)))) X2
       grind)
    | exact resolve eq33 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (σ (M.op X0 (M.op X0 X1)))) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1 X2
       have i₂ := eq9 X0 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 (M.op (σ X1) (σ X1)) (M.op X2 (σ (M.op X0 (M.op X0 X1)))) X2
       have j1 := eq9 (M.op (σ X1) (σ X1)) (M.op X2 (σ (M.op X0 (M.op X0 X1))))
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq677 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X4 X2))) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq11 (M.op X1 (M.op X1 X2)) X1 X2 X3 X4
       have i₂ := eq51 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq11 (M.op X1 (M.op X1 X2)) X1 X2 X3 X4
       have i₂ := eq51 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq51 eq11
    | exact resolve eq11 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2)))) = (M.op X5 (M.op X6 (M.op X6 (M.op X7 (M.op X4 (M.op X4 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq58 X3 (M.op X4 (M.op X4 X2)) X7 X5 X6
       have i₂ := eq11 (M.op X4 (M.op X4 X2)) X4 X2 X0 X1
       grind)
    | (have i₁ := eq58 X3 (M.op X4 (M.op X4 X2)) X7 X5 X6
       have i₂ := eq11 X0 X1 X2 (M.op X4 (M.op X4 X2)) X4
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1107 : ∀ X0 X1 X2 X3 X4 X5 X7 : G, (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2)))) = (M.op X5 (M.op X7 (M.op X4 (M.op X4 X2)))) := by
    intro X0 X1 X2 X3 X4 X5 X7
    first
    | (have i₁ := eq866 X0 X1 X2 X3 X4 X5 x X7
       have i₂ := eq18 X7 X4 X2 x x
       grind)
    | (have i₁ := eq866 X0 X1 X2 X3 X4 X5 X1 X1
       have i₂ := eq18 X1 X1 (M.op X4 (M.op X4 X2)) X3 X4
       grind)
    | exact superpose eq18 eq866
    | exact resolve eq866 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq1196 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op X0 X0)) = (M.op X4 (M.op X5 (M.op X5 (M.op X6 (M.op X2 (M.op X3 X0)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq58 X1 (M.op X2 (M.op X3 X0)) X6 X4 X5
       have i₂ := eq71 X0 X2 X3
       grind)
    | exact superpose eq71 eq58
    | exact resolve eq58 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq71
  have eq10426 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 (M.op X2 (M.op X2 X0)))) ∨ (M.op X2 (M.op X2 X0)) = X1 ∨ (M.op X2 (M.op X2 X0)) = (τ (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 (M.op X2 X0))
       have i₂ := eq77 X0 (σ X1) X2
       grind)
    | exact superpose eq77 eq9
    | (have j0 := eq9 (σ (M.op X0 X0)) (σ (M.op X1 (M.op X2 (M.op X2 X0))))
       have j1 := eq77 X0 (σ X1) X2
       grind)
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10436 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = X1 ∨ (σ (M.op X0 X0)) = (σ (M.op X1 (M.op X2 (M.op X2 X0)))) ∨ (M.op X2 (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10426 X0 X1 X2
       have i₂ := eq7 X1
       grind)
    | exact superpose eq7 eq10426
    | (have j0 := eq10426 X0 X1 X2
       grind)
    | exact resolve eq10426 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10426
  have eq10437 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 (M.op X2 (M.op X2 X0)))) ∨ (M.op X2 (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq10436 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10436
  have eq18153 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X2 (M.op X2 X0)) = (τ X1) ∨ X0 = X2 ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 X1 X2
       have i₂ := eq529 X2 X0 X1
       grind)
    | exact superpose eq529 eq77
    | (have j0 := eq77 X0 X1 X2
       have j1 := eq529 (σ (M.op X0 X0)) (M.op (σ X0) (σ X0)) X2
       grind)
    | exact resolve eq77 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq529
  have eq64811 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X2 X2)) = (σ (M.op X0 (M.op X1 (M.op X1 X2)))) ∨ (M.op X4 (M.op X4 X2)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10437 X2 X3 X4
       have i₂ := eq11 X3 X4 X2 X0 X1
       grind)
    | (have i₁ := eq10437 X2 X3 X4
       have i₂ := eq11 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq11 eq10437
    | (have j0 := eq10437 X2 X0 X1
       grind)
    | exact resolve eq10437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11 eq10437
  have eq80169 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X2)) ≠ (M.op X3 (M.op X3 X2)) ∨ (σ (M.op X2 X2)) = (σ (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq64811 X0 X1 X2 X3 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80170 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq80169 X0 X1 X2 x
       have j1 := eq64811 X0 X1 X2 x x
       grind)
    | exact resolve eq80169 eq64811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64811 eq80169
  have eq83184 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op X1 (M.op X2 (M.op X2 X3))))) = (σ (M.op X4 (M.op (M.op X1 (M.op X2 (M.op X2 X3))) (M.op X0 (M.op X1 (M.op X2 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq80170 X0 (M.op X0 (M.op X1 (M.op X1 X2))) (M.op X0 (M.op X1 (M.op X1 X2)))
       have i₂ := eq34 X0 X1 X2 X3
       grind)
    | (have i₁ := eq80170 X0 X3 (M.op X0 (M.op X1 (M.op X1 X2)))
       have i₂ := eq34 X0 X1 X2 X3
       grind)
    | exact superpose eq34 eq80170
    | exact resolve eq80170 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq83225 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (σ (M.op X5 X5)) = (σ (M.op X6 (M.op X0 (M.op X1 (M.op X1 (M.op X2 (M.op X3 (M.op X4 X5)))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq80170 X6 X5 X5
       have i₂ := eq1196 X5 X5 X3 X4 X0 X1 X2
       grind)
    | exact superpose eq1196 eq80170
    | exact resolve eq80170 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq83361 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op X1 (M.op X2 (M.op X2 X3))))) = (σ (M.op (M.op X4 X3) (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq80170 x X4 (M.op X4 X3)
       have i₂ := eq1107 X4 X4 X3 x X2 X0 X1
       grind)
    | (have i₁ := eq80170 x X4 (M.op X4 X3)
       have i₂ := eq1107 X1 X2 X3 X0 X4 x X4
       grind)
    | exact superpose eq1107 eq80170
    | exact resolve eq80170 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq80170
  have eq83727 : ∀ X0 X1 X2 X3 X4 : G, (σ (M.op X0 (M.op X1 (M.op X2 (M.op X2 X3))))) = (σ (M.op X4 (M.op X1 (M.op X2 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq83184 X0 X1 X2 X3 X4
       have i₂ := eq18 X1 X2 X3 (M.op X1 (M.op X2 (M.op X2 X3))) X0
       grind)
    | (have i₁ := eq83184 X1 X1 X2 X3 X4
       have i₂ := eq18 (M.op X1 (M.op X2 (M.op X2 X3))) X1 (M.op X2 (M.op X2 X3)) X3 X4
       grind)
    | exact superpose eq18 eq83184
    | exact resolve eq83184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83184
  have eq561362 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (τ X1) = (M.op X0 (M.op X0 x)) ∨ x = X0 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10
       have i₂ := eq18153 x X1 X0
       grind)
    | exact superpose eq18153 eq10
    | (have j1 := eq18153 x X1 X0
       grind)
    | exact resolve eq10 eq18153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18153
  have eq562964 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (M.op X0 x)) ∨ x = X0 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq561362 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561362
  have eq564374 : ∀ X0 X1 X2 : G, (τ X0) = (τ X1) ∨ x = X2 ∨ (M.op X2 x) = X2 ∨ x = X2 ∨ (M.op X2 x) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq562964 X2 X0
       have i₂ := eq562964 X2 X1
       grind)
    | exact superpose eq562964 eq562964
    | (have j0 := eq562964 X2 X1
       have j1 := eq562964 X2 X1
       grind)
    | exact resolve eq562964 eq562964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562964
  have eq565113 : ∀ X0 X1 X2 : G, (τ X0) = (τ X1) ∨ (M.op X2 x) = X2 ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq564374 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564374
  have eq569674 : ∀ X0 X1 X2 : G, (σ (τ X0)) = X1 ∨ (M.op X2 x) = X2 ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1
       have i₂ := eq565113 X1 X0 X2
       grind)
    | (have i₁ := eq8 X1
       have i₂ := eq565113 X0 X1 X2
       grind)
    | exact superpose eq565113 eq8
    | (have j1 := eq565113 X0 X1 X2
       grind)
    | exact resolve eq8 eq565113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565113
  have eq570324 : ∀ X0 X1 X2 : G, (M.op X2 x) = X2 ∨ X0 = X1 ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq569674 X0 X1 X2
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq569674
    | (have j0 := eq569674 X0 X1 X2
       grind)
    | exact resolve eq569674 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569674
  have eq578401 : ∀ X0 X1 : G, x ≠ X1 ∨ (M.op X0 x) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have j0 := eq570324 (M.op X0 x) X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578471 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq578401 X0 x
       have j1 := eq570324 (M.op X0 x) X0 X0
       grind)
    | exact resolve eq578401 eq570324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570324 eq578401
  have eq581200 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op x x)) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 x X0 x
       have i₂ := eq578471 X0
       grind)
    | exact superpose eq578471 eq15
    | (have j1 := eq578471 X0
       grind)
    | exact resolve eq15 eq578471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq581457 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 (σ x)) ∨ (τ X0) = x ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq31 X0 x
       have i₂ := eq578471 (τ X0)
       grind)
    | exact superpose eq578471 eq31
    | (have j0 := eq31 X0 x
       have j1 := eq578471 (τ X0)
       grind)
    | exact resolve eq31 eq578471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq581461 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op X1 (M.op X0 (σ (τ X0)))) ∨ (τ X0) = x ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 x X1
       have i₂ := eq578471 (τ X0)
       grind)
    | exact superpose eq578471 eq513
    | (have j0 := eq513 X0 x x
       have j1 := eq578471 (τ X0)
       grind)
    | exact resolve eq513 eq578471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq581482 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op X1 (M.op X0 (σ (τ X0)))) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have j0 := eq581461 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581461
  have eq581486 : ∀ X0 : G, (σ (τ X0)) = (M.op X0 (σ x)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have j0 := eq581457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581457
  have eq581550 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op X1 (M.op X0 X0)) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq581482 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq581482
    | (have j0 := eq581482 X0 X1
       grind)
    | exact resolve eq581482 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581482
  have eq581551 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq581486 X0
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq581486
    | (have j0 := eq581486 X0
       grind)
    | exact resolve eq581486 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581486
  have eq607715 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op x x))) ∨ x = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X3 X1 X2
       have i₂ := eq581200 (M.op X3 X1) X0
       grind)
    | (have i₁ := eq62 x x X2
       have i₂ := eq581200 X0 (M.op x x)
       grind)
    | exact superpose eq581200 eq62
    | (have j1 := eq581200 (M.op X3 X1) X1
       grind)
    | exact resolve eq62 eq581200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq581200
  have eq608870 : ∀ X1 X3 : G, (M.op x x) = (M.op X1 X1) ∨ x = (M.op X3 X1) := by
    intro X1 X3
    first
    | (have i₁ := eq607715 x X1 x X3
       have i₂ := eq17 x x x
       grind)
    | (have i₁ := eq607715 x X1 (M.op x (M.op x x)) X3
       have i₂ := eq17 (M.op x (M.op x x)) x X3
       grind)
    | exact superpose eq17 eq607715
    | (have j0 := eq607715 x X1 x X3
       grind)
    | exact resolve eq607715 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607715
  have eq619879 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 x)) ∨ (M.op X0 X0) = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 X0 X1 X2
       have i₂ := eq608870 X0 X2
       grind)
    | exact superpose eq608870 eq6
    | (have j1 := eq608870 X0 x
       grind)
    | exact resolve eq6 eq608870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620301 : ∀ X1 X2 X3 X4 : G, x = (M.op X3 (M.op X4 x)) ∨ (M.op x x) = (M.op (M.op X1 (M.op X1 X2)) (M.op X1 (M.op X1 X2))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq18 X3 X1 X2 X3 X4
       have i₂ := eq608870 (M.op X1 (M.op X1 X2)) X3
       grind)
    | exact superpose eq608870 eq18
    | (have j1 := eq608870 (M.op X1 (M.op X1 X2)) X3
       grind)
    | exact resolve eq18 eq608870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq620305 : ∀ X0 X2 X3 X4 : G, (M.op X0 x) = (M.op X4 x) ∨ (M.op x x) = (M.op (M.op X2 (M.op X2 X3)) (M.op X2 (M.op X2 X3))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq89 X3 x X2 X3 X4
       have i₂ := eq608870 (M.op x (M.op x X2)) X3
       grind)
    | exact superpose eq608870 eq89
    | (have j1 := eq608870 (M.op X2 (M.op X2 X3)) X3
       grind)
    | exact resolve eq89 eq608870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq620365 : ∀ X0 X2 X3 X4 : G, (σ (M.op X4 x)) = (σ (M.op X0 x)) ∨ (M.op x x) = (M.op (M.op X2 (M.op X2 X3)) (M.op X2 (M.op X2 X3))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq83727 X0 X3 X2 X3 X4
       have i₂ := eq608870 (M.op X2 (M.op X2 X3)) X3
       grind)
    | exact superpose eq608870 eq83727
    | (have j1 := eq608870 (M.op X2 (M.op X2 X3)) X3
       grind)
    | exact resolve eq83727 eq608870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83727
  have eq621076 : ∀ X0 X3 X4 : G, (M.op x x) = (M.op X3 X3) ∨ (σ (M.op X4 x)) = (σ (M.op X0 x)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq620365 X0 x X3 X4
       have i₂ := eq6 X3 (M.op x (M.op x X3)) x
       grind)
    | (have i₁ := eq620365 X0 x X3 X4
       have i₂ := eq6 (M.op x (M.op x X3)) x x
       grind)
    | exact superpose eq6 eq620365
    | (have j0 := eq620365 X0 x X3 X4
       grind)
    | exact resolve eq620365 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620365
  have eq621134 : ∀ X0 X3 X4 : G, (M.op x x) = (M.op X3 X3) ∨ (M.op X0 x) = (M.op X4 x) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq620305 X0 x X3 X4
       have i₂ := eq6 X3 (M.op x (M.op x X3)) x
       grind)
    | (have i₁ := eq620305 X0 x X3 X4
       have i₂ := eq6 (M.op x (M.op x X3)) x x
       grind)
    | exact superpose eq6 eq620305
    | (have j0 := eq620305 X0 x X3 X4
       grind)
    | exact resolve eq620305 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620305
  have eq621138 : ∀ X2 X3 X4 : G, (M.op x x) = (M.op X2 X2) ∨ x = (M.op X3 (M.op X4 x)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq620301 x X2 X3 X4
       have i₂ := eq6 X2 (M.op x (M.op x X2)) x
       grind)
    | (have i₁ := eq620301 x X2 X3 X4
       have i₂ := eq6 (M.op x (M.op x X2)) x X2
       grind)
    | exact superpose eq6 eq620301
    | (have j0 := eq620301 x X2 X3 X4
       grind)
    | exact resolve eq620301 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620301
  have eq728373 : ∀ X0 X1 X2 : G, (M.op x x) = (M.op X2 X2) ∨ (M.op X0 x) = X1 ∨ x = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq578471 X1
       have i₂ := eq621134 X1 X2 X0
       grind)
    | (have i₁ := eq578471 X1
       have i₂ := eq621134 X0 X2 X1
       grind)
    | exact superpose eq621134 eq578471
    | (have j0 := eq578471 X1
       have j1 := eq621134 X0 X2 x
       grind)
    | exact resolve eq578471 eq621134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621134
  have eq729542 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op X2 X1) ∨ x = (M.op X3 (M.op X4 x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq608870 X1 X2
       have i₂ := eq621138 X0 X3 X4
       grind)
    | (have i₁ := eq608870 X1 X3
       have i₂ := eq621138 x X3 X4
       grind)
    | exact superpose eq621138 eq608870
    | (have j0 := eq608870 X1 X2
       have j1 := eq621138 X2 X3 X4
       grind)
    | exact resolve eq608870 eq621138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739032 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op X0 (M.op X1 X1)) ∨ x = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10
       have i₂ := eq581550 X1 X0
       grind)
    | exact superpose eq581550 eq10
    | (have j1 := eq581550 X1 X1
       grind)
    | exact resolve eq10 eq581550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581550
  have eq740200 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ x = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq739032 (M.op X1 X1) X1
       have i₂ := eq51 X1 X1 X0
       grind)
    | (have i₁ := eq739032 (M.op X1 X1) X1
       have i₂ := eq51 X0 X1 X1
       grind)
    | exact superpose eq51 eq739032
    | (have j0 := eq739032 X0 X1
       grind)
    | exact resolve eq739032 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq739032
  have eq747310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op X2 X1) ∨ (M.op X3 x) = X4 ∨ x = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq608870 X1 X2
       have i₂ := eq728373 X3 X4 X0
       grind)
    | (have i₁ := eq608870 X1 X3
       have i₂ := eq728373 X0 X1 x
       grind)
    | exact superpose eq728373 eq608870
    | (have j0 := eq608870 X1 X2
       have j1 := eq728373 X3 X4 X2
       grind)
    | exact resolve eq608870 eq728373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748042 : ∀ X0 X1 X2 X3 : G, (M.op x x) = (M.op X3 X3) ∨ (M.op X1 (M.op X2 X0)) = X0 ∨ x = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 x X2 X3
       have i₂ := eq728373 x X1 X2
       grind)
    | (have i₁ := eq17 X0 X2 X3
       have i₂ := eq728373 X0 (M.op X0 X0) X2
       grind)
    | exact superpose eq728373 eq17
    | (have j1 := eq728373 x (M.op X3 X3) X3
       grind)
    | exact resolve eq17 eq728373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq748335 : ∀ X0 X1 X2 : G, x ≠ (M.op X1 x) ∨ (M.op x x) = (M.op X2 X2) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq728373 x (M.op X2 X2) X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751843 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) ≠ x ∨ (M.op X0 X0) = (M.op X1 X1) ∨ x = X2 ∨ x = (M.op X3 (M.op X4 x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq748335 X0 x X2
       have i₂ := eq621138 X2 X3 X4
       grind)
    | (have i₁ := eq748335 X0 x X2
       have i₂ := eq621138 x X3 X4
       grind)
    | exact superpose eq621138 eq748335
    | (have j0 := eq748335 X2 X1 X2
       have j1 := eq621138 X2 X3 X4
       grind)
    | exact resolve eq748335 eq621138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751845 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) ≠ x ∨ (M.op X0 X0) = (M.op X1 X1) ∨ x = X2 ∨ (M.op X3 x) = X4 ∨ x = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq748335 X0 x X2
       have i₂ := eq728373 X0 X1 X2
       grind)
    | (have i₁ := eq748335 X0 x X2
       have i₂ := eq728373 X0 X1 x
       grind)
    | exact superpose eq728373 eq748335
    | (have j0 := eq748335 X2 X1 X2
       have j1 := eq728373 X3 X4 X2
       grind)
    | exact resolve eq748335 eq728373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748335
  have eq751861 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = X2 ∨ (M.op X3 x) = X4 ∨ x = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq751845 X0 X1 X2 X3 X4
       have j1 := eq747310 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq751845 eq747310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747310 eq751845
  have eq751862 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = X2 ∨ x = (M.op X3 (M.op X4 x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq751843 X0 X1 X2 X3 X4
       have j1 := eq729542 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq751843 eq729542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729542 eq751843
  have eq788734 : ∀ X0 X1 X2 : G, (M.op x x) ≠ (M.op X1 (M.op X2 x)) ∨ (M.op X0 X0) = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq619879 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619879
  have eq803609 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op X2 X1) ∨ (σ (M.op X3 x)) = (σ (M.op X4 x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq608870 X1 X2
       have i₂ := eq621076 X4 X0 X3
       grind)
    | (have i₁ := eq608870 X1 X3
       have i₂ := eq621076 X0 x X4
       grind)
    | exact superpose eq621076 eq608870
    | (have j0 := eq608870 X1 X2
       have j1 := eq621076 X4 X3 X3
       grind)
    | exact resolve eq608870 eq621076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904214 : ∀ X0 X1 X2 : G, (M.op x x) ≠ (M.op X1 X0) ∨ (M.op x x) = (M.op X2 X2) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq788734 X2 X1 X0
       have i₂ := eq578471 X0
       grind)
    | exact superpose eq578471 eq788734
    | (have j0 := eq788734 X2 X1 X2
       have j1 := eq578471 X0
       grind)
    | exact resolve eq788734 eq578471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578471
  have eq904295 : ∀ X1 X2 : G, x ≠ (M.op x x) ∨ (M.op x x) = (M.op X2 X2) ∨ (M.op x x) = (M.op (M.op X1 x) (M.op X1 x)) := by
    intro X1 X2
    first
    | (have i₁ := eq788734 X2 x X1
       have i₂ := eq608870 (M.op X1 x) x
       grind)
    | exact superpose eq608870 eq788734
    | (have j0 := eq788734 X2 X1 X2
       have j1 := eq608870 X2 x
       grind)
    | exact resolve eq788734 eq608870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608870
  have eq904333 : ∀ X2 : G, x ≠ (M.op x x) ∨ (M.op x x) = (M.op X2 X2) := by
    intro X2
    first
    | (have j0 := eq904295 x X2
       have j1 := eq788734 X2 x X2
       grind)
    | exact resolve eq904295 eq788734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788734 eq904295
  have eq907804 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ x ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ (M.op X2 x)) = (σ (M.op X3 x)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq904333 X2
       have i₂ := eq621076 X0 X3 x
       grind)
    | (have i₁ := eq904333 X2
       have i₂ := eq621076 X0 x x
       grind)
    | exact superpose eq621076 eq904333
    | (have j1 := eq621076 X3 X3 X2
       grind)
    | exact resolve eq904333 eq621076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621076
  have eq907806 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ x ∨ (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op X2 (M.op X3 x)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq904333 X2
       have i₂ := eq621138 X2 X3 x
       grind)
    | (have i₁ := eq904333 X2
       have i₂ := eq621138 x X3 x
       grind)
    | exact superpose eq621138 eq904333
    | (have j1 := eq621138 X2 X2 X3
       grind)
    | exact resolve eq904333 eq621138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621138
  have eq907808 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ x ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X2 x) = X3 ∨ x = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq904333 X2
       have i₂ := eq728373 X0 X1 X2
       grind)
    | (have i₁ := eq904333 X2
       have i₂ := eq728373 X0 X1 x
       grind)
    | exact superpose eq728373 eq904333
    | (have j1 := eq728373 X2 X3 X2
       grind)
    | exact resolve eq904333 eq728373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728373 eq904333
  have eq907846 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X2 x) = X3 ∨ x = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq907808 X0 X1 X2 X3
       have j1 := eq751861 X0 X1 X3 X2 X3
       grind)
    | exact resolve eq907808 eq751861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751861 eq907808
  have eq907847 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op X2 (M.op X3 x)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq907806 X0 X1 X2 X3
       have j1 := eq751862 X0 X1 (M.op X2 (M.op X3 x)) X2 X3
       grind)
    | exact resolve eq907806 eq751862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751862 eq907806
  have eq907849 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (M.op X2 x)) = (σ (M.op X3 x)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq907804 X0 X1 X2 X3
       have j1 := eq803609 X0 X1 X2 X2 X3
       grind)
    | exact resolve eq907804 eq803609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803609 eq907804
  have eq942409 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 x)) = X1 ∨ (M.op X2 X2) = (M.op X3 X3) ∨ x = (τ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1
       have i₂ := eq907846 X2 X3 X0 (τ X1)
       grind)
    | exact superpose eq907846 eq8
    | (have j1 := eq907846 X2 X3 X2 (τ X1)
       grind)
    | exact resolve eq8 eq907846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942421 : ∀ X0 X1 X2 X3 : G, x ≠ (M.op X1 x) ∨ (M.op X2 X2) = (M.op X3 X3) ∨ x = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq907846 X2 X3 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907846
  have eq1302859 : ∀ X0 X2 : G, (σ (M.op x x)) ≠ X0 ∨ (τ X0) = x ∨ (M.op x x) = (M.op X2 X2) ∨ x = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq740200 x X0
       have i₂ := eq748042 X0 (M.op x X0) x X2
       grind)
    | exact superpose eq748042 eq740200
    | (have j0 := eq740200 X0 X0
       have j1 := eq748042 (τ X0) x X2 X2
       grind)
    | exact resolve eq740200 eq748042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740200 eq748042
  have eq1302903 : ∀ X0 X2 : G, (M.op x x) = (M.op X2 X2) ∨ (τ X0) = x ∨ x = X0 := by
    intro X0 X2
    first
    | (have j0 := eq1302859 X0 X2
       have j1 := eq942409 X0 X0 x X2
       grind)
    | exact resolve eq1302859 eq942409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942409 eq1302859
  have eq1303789 : ∀ X0 X1 : G, (M.op x x) = (M.op X1 X1) ∨ (σ x) = X0 ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0
       have i₂ := eq1302903 X0 X1
       grind)
    | exact superpose eq1302903 eq8
    | (have j1 := eq1302903 X0 X1
       grind)
    | exact resolve eq8 eq1302903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302903
  have eq1304585 : ∀ X1 X2 X3 : G, x = (M.op x x) ∨ (M.op X2 X2) = (M.op X1 X1) ∨ (σ x) = X3 ∨ x = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq907847 X2 X1 (M.op x x) x
       have i₂ := eq1303789 X3 (M.op x x)
       grind)
    | exact superpose eq1303789 eq907847
    | (have j0 := eq907847 X2 X1 X2 X3
       have j1 := eq1303789 X3 X1
       grind)
    | exact resolve eq907847 eq1303789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907847 eq1303789
  have eq1304777 : ∀ X1 X2 X3 : G, (M.op X2 X2) = (M.op X1 X1) ∨ (σ x) = X3 ∨ x = X3 := by
    intro X1 X2 X3
    first
    | (have j0 := eq1304585 X1 X2 X3
       have j1 := eq942421 X3 X1 X2 X1
       grind)
    | exact resolve eq1304585 eq942421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942421 eq1304585
  have eq1309376 : ∀ X0 X1 X2 : G, x ≠ (σ x) ∨ (M.op X2 X2) = (M.op X1 X1) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1304777 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304777
  have eq1627032 : ∀ X0 X1 : G, (M.op x x) ≠ X0 ∨ (M.op x x) = (M.op X1 X1) ∨ x = (σ x) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq904214 (σ x) X0 X1
       have i₂ := eq581551 X0
       grind)
    | exact superpose eq581551 eq904214
    | (have j0 := eq904214 (σ x) X1 X1
       have j1 := eq581551 X0
       grind)
    | exact resolve eq904214 eq581551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581551 eq904214
  have eq1627044 : ∀ X0 X1 : G, (M.op x x) ≠ X0 ∨ (M.op x x) = (M.op X1 X1) ∨ (τ X0) = x := by
    intro X0 X1
    first
    | (have j0 := eq1627032 X0 X1
       have j1 := eq1309376 (τ X0) X1 x
       grind)
    | exact resolve eq1627032 eq1309376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309376 eq1627032
  have eq1627118 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) ∨ x = (τ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq1627044 (M.op x x) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627044
  have eq1634741 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) ∨ (M.op x x) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op x x)
       have i₂ := eq1627118 X0
       grind)
    | exact superpose eq1627118 eq8
    | (have j1 := eq1627118 X0
       grind)
    | exact resolve eq8 eq1627118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627118
  have eq1635202 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (σ x) ∨ (M.op x x) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1634741 X0
       have i₂ := eq1634741 x
       grind)
    | (have i₁ := eq1634741 X0
       have i₂ := eq1634741 X0
       grind)
    | exact superpose eq1634741 eq1634741
    | exact resolve eq1634741 eq1634741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1636287 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (M.op x x) = (σ x) := by
    intro X0
    grind
  clear eq1634741
  have eq1636367 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op x x) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq1635202 X0 X1
       grind)
    | exact resolve eq1635202 eq1636287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635202 eq1636287
  have eq1645996 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ x)) = (M.op X0 (σ x)) ∨ (M.op X2 X2) = (M.op X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40 X0 x X3
       have i₂ := eq1636367 X0 X1
       grind)
    | exact superpose eq1636367 eq40
    | (have j1 := eq1636367 X2 X3
       grind)
    | exact resolve eq40 eq1636367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1636367
  have eq1729115 : ∀ X0 X1 X2 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X2 X2) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10
       have i₂ := eq1645996 X0 (σ x) X2 X1
       grind)
    | (have i₁ := eq10
       have i₂ := eq1645996 (σ x) X0 X2 X1
       grind)
    | exact superpose eq1645996 eq10
    | (have j1 := eq1645996 X0 X1 X2 X1
       grind)
    | exact resolve eq10 eq1645996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645996
  have eq1771666 : ∀ X0 X1 X2 : G, (σ (M.op x x)) ≠ (σ (M.op X0 x)) ∨ (M.op X2 X2) = (M.op X1 X1) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1729115 (σ X0) X1 X2
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq1729115
    | (have j0 := eq1729115 X0 X1 X2
       have j1 := eq9 (M.op X2 X2) (M.op X1 X1)
       grind)
    | exact resolve eq1729115 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729115
  have eq1771673 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 X1) ∨ x = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1771666 X0 X1 X2
       have j1 := eq907849 X2 X1 X2 x
       grind)
    | exact resolve eq1771666 eq907849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907849 eq1771666
  have eq1777033 : ∀ X0 X1 : G, x ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10
       have i₂ := eq1771673 (M.op (σ x) (σ x)) X1 X0
       grind)
    | exact superpose eq1771673 eq10
    | (have j1 := eq1771673 X0 X1 X0
       grind)
    | exact resolve eq10 eq1771673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1777659 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1777033 X0 X1
       have j1 := eq1771673 X0 X1 X0
       grind)
    | exact resolve eq1777033 eq1771673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771673 eq1777033
  have eq1782898 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83225 x x x x x X0 (M.op x (M.op x (M.op x (M.op x (M.op x (M.op x X0))))))
       have i₂ := eq1777659 (M.op x (M.op x (M.op x (M.op x (M.op x (M.op x X0)))))) X1
       grind)
    | (have i₁ := eq83225 x x x x x X0 (M.op x (M.op x (M.op x (M.op x (M.op x (M.op x X0))))))
       have i₂ := eq1777659 X1 (M.op x (M.op x (M.op x (M.op x (M.op x (M.op x X0))))))
       grind)
    | exact superpose eq1777659 eq83225
    | exact resolve eq83225 eq1777659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83225
  have eq1783514 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq1777659 (M.op X2 X0) X1
       grind)
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq1777659 X0 (M.op X2 X0)
       grind)
    | exact superpose eq1777659 eq177
    | exact resolve eq177 eq1777659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1783633 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq10
       have i₂ := eq1777659 (σ x) X0
       grind)
    | (have i₁ := eq10
       have i₂ := eq1777659 X0 (σ x)
       grind)
    | exact superpose eq1777659 eq10
    | exact resolve eq10 eq1777659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1785087 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1783633 X1
       have i₂ := eq1777659 x X0
       grind)
    | (have i₁ := eq1783633 X1
       have i₂ := eq1777659 X0 x
       grind)
    | exact superpose eq1777659 eq1783633
    | exact resolve eq1783633 eq1777659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777659 eq1783633
  have eq1785927 : ∀ X0 X1 X2 X5 : G, (M.op X0 (M.op X1 (M.op X1 X2))) ≠ (σ (M.op X5 X5)) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq1785087 X5 (M.op x (M.op x X2))
       have i₂ := eq677 x x X2 X0 X1
       grind)
    | (have i₁ := eq1785087 X0 (M.op x (M.op x X2))
       have i₂ := eq677 X0 X1 X2 (M.op x (M.op x X2)) x
       grind)
    | exact superpose eq677 eq1785087
    | exact resolve eq1785087 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq1787095 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X4) ≠ (σ (M.op X0 (M.op X1 (M.op X2 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1785087 (M.op x X3) X4
       have i₂ := eq83361 X0 X1 X2 X3 x
       grind)
    | exact superpose eq83361 eq1785087
    | exact resolve eq1785087 eq83361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83361 eq1785087
  have eq2919030 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (M.op X3 X3)) ∨ (M.op X2 X2) = (τ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1783514 X2 X3 X1
       have i₂ := eq1782898 X2 X0
       grind)
    | (have i₁ := eq1783514 X2 X3 X1
       have i₂ := eq1782898 X0 X2
       grind)
    | exact superpose eq1782898 eq1783514
    | (have j0 := eq1783514 X0 X3 X1
       grind)
    | exact resolve eq1783514 eq1782898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782898 eq1783514
  have eq2963763 : ∀ X0 X1 X5 X6 : G, (σ (τ X0)) ≠ (M.op X1 X1) ∨ (σ (M.op X6 X6)) = (M.op X0 (σ (M.op X5 X5))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq1787095 (M.op x (M.op x (M.op x x))) x x x X1
       have i₂ := eq2919030 X5 X0 (M.op x (M.op x (M.op x x))) X6
       grind)
    | exact superpose eq2919030 eq1787095
    | (have j1 := eq2919030 X5 X0 x X6
       grind)
    | exact resolve eq1787095 eq2919030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787095 eq2919030
  have eq2963847 : ∀ X0 X1 X5 X6 : G, (M.op X1 X1) ≠ X0 ∨ (σ (M.op X6 X6)) = (M.op X0 (σ (M.op X5 X5))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq2963763 X0 X1 X5 X6
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq2963763
    | (have j0 := eq2963763 X0 X1 X5 X6
       grind)
    | exact resolve eq2963763 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963763
  have eq2964132 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2963847 (M.op X1 X1) X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963847
  have eq2965909 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X2)) = (M.op (M.op X3 X3) (M.op (M.op X0 X0) (σ (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2964132 X2 X3 x
       have i₂ := eq2964132 x X0 X1
       grind)
    | exact superpose eq2964132 eq2964132
    | exact resolve eq2964132 eq2964132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2966599 : ∀ X0 X1 X2 X4 : G, (σ (M.op X4 X4)) ≠ (M.op X1 (M.op (M.op X2 X2) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1785927 X1 (M.op X2 X2) (σ (M.op x x)) X4
       have i₂ := eq2964132 X0 X2 x
       grind)
    | exact superpose eq2964132 eq1785927
    | exact resolve eq1785927 eq2964132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785927 eq2964132
  have eq2966672 : False := by
    have f2966672_8 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 X2)) = (M.op (M.op X3 X3) (M.op (M.op X0 X0) (σ (M.op X1 X1)))) := by
      intro X0 X1 X2 X3
      grind
    have f2966672_9 : ∀ X0 X1 X2 X3 : G, (σ (M.op X3 X3)) ≠ (M.op X1 (M.op (M.op X2 X2) (σ (M.op X0 X0)))) := by
      intro X0 X1 X2 X3
      grind
    have f2966672_15 : False := by
      first
      | exact resolve f2966672_8 f2966672_9
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f2966672_15
  exact eq2966672
