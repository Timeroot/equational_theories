import equational_theories.Definability.AutBox

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Every bijection of a model of `Equation1448` respecting `(y ◇ (x ◇ x))` respects `◇`.
Vampire refutation replayed step by step. -/
private theorem haut0 : ∀ {G : Type} [Finite G] (M : Magma G), satisfies G Law1448 →
    ∀ σ τ : G → G, (∀ a : G, τ (σ a) = a) → (∀ a : G, σ (τ a) = a) →
    (∀ a b : G, σ (@evalInMagma _ _ M ![a, b] (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))
      = @evalInMagma _ _ M ![σ a, σ b] (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) →
    ∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b) := by
  intro G _ M hM σ τ h1 h2 hw a b
  have h := (@Law1448.models_iff G M).mp hM
  simp only [evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] at hw
  by_contra nh
  have eq6 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq7 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq8 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X0 X0))) = (M.op (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    grind
  have eq10 : (σ (M.op a b)) ≠ (M.op (σ a) (σ b)) := by grind
  clear h hw h1 h2 nh hM
  have eq11 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) (M.op X3 (M.op X0 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 (M.op X0 X1) (M.op X0 (M.op X2 X1)) X3
       have i₂ := eq6 X0 X1 X2
       grind)
    | exact superpose eq6 eq6
    | exact resolve eq6 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op X2 X3))) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 X1 (M.op X0 (M.op X2 X3)) (M.op X0 X3)
       have i₂ := eq6 X0 X3 X2
       grind)
    | exact superpose eq6 eq6
    | exact resolve eq6 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 (M.op X0 X1) (M.op X2 X1) X0
       have i₂ := eq6 X0 X1 X2
       grind)
    | exact superpose eq6 eq6
    | exact resolve eq6 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1) x X1
       have i₂ := eq6 X0 X1 x
       grind)
    | exact superpose eq6 eq12
    | exact resolve eq12 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (σ (M.op (τ X0) (M.op X1 X1))) = (M.op X0 (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq9
    | exact resolve eq9 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (σ (M.op X1 (M.op (τ X0) (τ X0)))) = (M.op (σ X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq9
    | exact resolve eq9 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (σ X1) (σ X1))) (M.op X2 (σ (M.op X0 (M.op X1 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 X2 (M.op (σ X1) (σ X1)) (σ X0)
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq6
    | exact resolve eq6 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 (M.op X1 X1))) (M.op (σ X0) (M.op X2 (M.op (σ X1) (σ X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 (σ X0) (M.op (σ X1) (σ X1)) X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq6
    | exact resolve eq6 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op (M.op X1 (M.op X0 X2)) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 X2) (M.op X0 (M.op X2 (M.op x x)))
       have i₂ := eq12 X2 X0 x x
       grind)
    | exact superpose eq12 eq13
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12
  have eq81 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6 X0 X0 (M.op X0 X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq6
    | exact resolve eq6 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq95 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (M.op X0 X0) X1
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq81
    | exact resolve eq81 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6 (M.op X0 X0) X1 X0
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq6
    | exact resolve eq6 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0)
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq25
    | exact resolve eq25 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq120 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op X2 X1))) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op X2 X1))
       have i₂ := eq13 (M.op (τ X0) (τ X0)) X1 X2
       grind)
    | exact superpose eq13 eq26
    | exact resolve eq26 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq275 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 X2) (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X2)
       have i₂ := eq11 (M.op X0 (M.op X1 X2)) X2 X1 X0
       grind)
    | exact superpose eq11 eq11
    | exact resolve eq11 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11
  have eq343 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) (M.op X1 (σ (M.op X2 X0)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op X0 X0) X1
       have i₂ := eq81 X0 X0
       grind)
    | exact superpose eq81 eq31
    | exact resolve eq31 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq81
  have eq382 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (τ X1) X0)) (M.op X1 (σ (M.op X2 X0)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq343 X0 X1 X2
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq343
    | exact resolve eq343 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq343
  have eq395 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6 X0 X1 (M.op X0 X0)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq6
    | exact resolve eq6 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq461 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (M.op (σ X0) (M.op X3 (M.op (σ X0) (M.op X2 (M.op (σ X1) (σ X1)))))) (σ (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (σ (M.op X0 (M.op X1 X1))) (M.op (σ X0) (M.op X2 (M.op (σ X1) (σ X1)))) X2
       have i₂ := eq32 X0 X1 X2
       grind)
    | exact superpose eq32 eq13
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13 eq32
  have eq1343 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq275 (M.op X0 X0) X1 X0
       have i₂ := eq105 X0 (M.op X1 X0)
       grind)
    | exact superpose eq105 eq275
    | exact resolve eq275 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1347 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1 (M.op X0 X0)
       have i₂ := eq395 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq395 eq275
    | exact resolve eq275 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq1393 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1343 X0 X1
       have i₂ := eq395 X0 X0
       grind)
    | exact superpose eq395 eq1343
    | exact resolve eq1343 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1470 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 X1 (M.op X2 X0) (M.op X0 X0)
       have i₂ := eq1393 X0 X2
       grind)
    | exact superpose eq1393 eq6
    | exact resolve eq6 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2312 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op X0 X1) X0 X1
       have i₂ := eq1470 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1470 eq59
    | exact resolve eq59 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1470
  have eq12112 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ (M.op (M.op (τ X0) (τ X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1347 X0 (σ (M.op (M.op (M.op (τ X0) (τ X0)) X1) (M.op x X1)))
       have i₂ := eq120 X0 X1 x
       grind)
    | exact superpose eq120 eq1347
    | exact resolve eq1347 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1347
  have eq18824 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (τ X1) (M.op X2 X0))) (M.op X1 (σ X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq382 (M.op X2 X0) X1 (M.op X0 X0)
       have i₂ := eq1393 X0 X2
       grind)
    | exact superpose eq1393 eq382
    | exact resolve eq382 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq1393
  have eq20486 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) (M.op X0 (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18824 X1 X0 (M.op (τ X0) X1)
       have i₂ := eq2312 (τ X0) X1
       grind)
    | exact superpose eq2312 eq18824
    | exact resolve eq18824 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312 eq18824
  have eq21224 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X1) (τ X1))) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20486 X1 (τ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq20486
    | exact resolve eq20486 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20486
  have eq21929 : ∀ X0 X2 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ (M.op (M.op (τ X0) (τ X0)) (M.op X2 X2)))) := by
    intro X0 X2
    first
    | (have i₁ := eq461 (M.op (τ X0) (τ X0)) X2 x X0
       have i₂ := eq21224 (M.op (σ (M.op (τ X0) (τ X0))) (M.op x (M.op (σ X2) (σ X2)))) X0
       grind)
    | exact superpose eq21224 eq461
    | exact resolve eq461 eq21224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq21224
  have eq22149 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq21929 X0 x
       have i₂ := eq12112 X0 (M.op x x)
       grind)
    | exact superpose eq12112 eq21929
    | exact resolve eq21929 eq12112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12112 eq21929
  have eq22568 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op X1 (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq22149 X0
       grind)
    | exact superpose eq22149 eq9
    | exact resolve eq9 eq22149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22149
  have eq22653 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22568 X0 X1
       have i₂ := eq395 (τ X0) (τ X0)
       grind)
    | exact superpose eq395 eq22568
    | exact resolve eq22568 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22568
  have eq22684 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22653 X0 X1
       have i₂ := eq395 X0 X0
       grind)
    | exact superpose eq395 eq22653
    | exact resolve eq22653 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq22653
  have eq26387 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22684 (σ X0) X1
       have i₂ := eq7 X0
       grind)
    | exact superpose eq7 eq22684
    | exact resolve eq22684 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22684
  have eq29602 : (σ (M.op a b)) ≠ (σ (M.op a b)) := by
    first
    | (have i₁ := eq10
       have i₂ := eq26387 b a
       grind)
    | exact superpose eq26387 eq10
    | (have r₁ := eq10
       have r₂ := eq26387 b a
       grind)
    | exact resolve eq10 eq26387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26387
  have eq29801 : False := by grind
  exact eq29801
