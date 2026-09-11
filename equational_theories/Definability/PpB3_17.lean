import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_pxy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X1) (M.op (M.op X1 X2) (M.op X0 X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq57
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq29 X0 X0
       grind)
    | exact superpose eq29 eq57
    | exact resolve eq57 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq60 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq59
    | exact resolve eq59 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq58
  have eq66 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0 (σ X0)
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq66
    | exact resolve eq66 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq94 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq61 (M.op X0 X0)
       grind)
    | exact superpose eq61 eq82
    | exact resolve eq82 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq143 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0 (τ X0)
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq75
    | exact resolve eq75 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq156 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq143 X0
       have i₂ := eq60 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq143
    | exact resolve eq143 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq247 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq156 X0
       have i₂ := eq53 X0 X0 X0 X1
       grind)
    | exact superpose eq53 eq156
    | exact resolve eq156 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq263 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X1) X3) (M.op X1 X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq53 (M.op X0 X1) X3 X1 x
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op X0 X1) X3)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq247 (M.op (M.op X2 X3) (M.op (M.op X0 X1) X3)) X0 X1
       have i₂ := eq9 X2 X3 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq247
    | exact resolve eq247 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq247 (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X3) X0 X1
       have i₂ := eq247 X2 X3 (M.op X0 X1)
       grind)
    | exact superpose eq247 eq247
    | exact resolve eq247 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq247 (M.op X1 (M.op (M.op X0 X2) X0)) X0 X2
       have i₂ := eq247 X1 (M.op X0 X2) X0
       grind)
    | exact superpose eq247 eq247
    | exact resolve eq247 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X1 X2)) X0) = (M.op (M.op X3 (M.op X4 (M.op (M.op X0 X1) X2))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op X1 X2) (M.op (M.op X0 X1) X2) X4
       have i₂ := eq263 X0 X1 X2
       grind)
    | exact superpose eq263 eq53
    | exact resolve eq53 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op (M.op X1 X2) X4)) = (M.op (M.op X3 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 X4 (M.op X1 X2) (M.op (M.op X0 X1) X2)
       have i₂ := eq263 X0 X1 X2
       grind)
    | exact superpose eq263 eq53
    | exact resolve eq53 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq366 X0 X1 X2 X3 x
       have i₂ := eq290 X1 X2 X3 x
       grind)
    | exact superpose eq290 eq366
    | exact resolve eq366 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq369 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X1 X2)) X0) = (M.op (M.op X3 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq365 X0 X1 X2 X3 x
       have i₂ := eq291 (M.op X0 X1) X2 X3 x
       grind)
    | exact superpose eq291 eq365
    | exact resolve eq365 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq365
  have eq397 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq295 (M.op X0 X1) X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq295
    | exact resolve eq295 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X0) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq295 X0 (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X0) X3)) X1
       have i₂ := eq9 X2 X3 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq9 eq295
    | exact resolve eq295 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op (M.op (M.op X1 X0) X1) X3)) X0) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq247 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq295 X1 (M.op X2 (M.op (M.op (M.op X1 X0) X1) X3)) X0
       grind)
    | exact superpose eq295 eq247
    | exact resolve eq247 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X1 X0) X1)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq427 X0 X1 X2 X3
       have i₂ := eq369 (M.op (M.op X1 X0) X1) X3 X0 X2
       grind)
    | (have i₁ := eq427 X0 X1 X3 X2
       have i₂ := eq369 X0 (M.op (M.op X1 X0) X1) X2 X3
       grind)
    | exact superpose eq369 eq427
    | exact resolve eq427 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq444 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X3 X1)) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq404 X0 X1 X2 X3
       have i₂ := eq369 (M.op (M.op X0 X1) X0) X3 X1 (M.op X2 X3)
       grind)
    | (have i₁ := eq404 X0 X0 X2 X2
       have i₂ := eq369 X0 (M.op (M.op X0 X0) X0) X2 (M.op X2 X2)
       grind)
    | exact superpose eq369 eq404
    | exact resolve eq404 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq450 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X2 (M.op X3 X0)) X0) X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq432 X0 x X2 X3
       have i₂ := eq295 x (M.op X2 (M.op X3 X0)) X0
       grind)
    | exact superpose eq295 eq432
    | exact resolve eq432 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq455 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X3 X1)) X1) = X2 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq444 x X1 X2 X3
       have i₂ := eq295 x (M.op (M.op X2 X3) (M.op X3 X1)) X1
       grind)
    | exact superpose eq295 eq444
    | exact resolve eq444 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq444
  have eq538 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq397 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3
       have i₂ := eq263 X0 X1 X2
       grind)
    | exact superpose eq263 eq397
    | exact resolve eq397 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq397 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq247 X1 X0 X0
       grind)
    | exact superpose eq247 eq397
    | exact resolve eq397 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op X2 X1)
       have i₂ := eq397 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq397 eq9
    | exact resolve eq9 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq450 X1 (M.op (M.op X0 X2) X1) X2
       have i₂ := eq263 X0 X2 X1
       grind)
    | exact superpose eq263 eq450
    | exact resolve eq450 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq247 (M.op X0 (M.op X1 (M.op X1 X2))) X1 X2
       have i₂ := eq450 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq450 eq247
    | exact resolve eq247 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 (M.op (M.op X2 X3) X1)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq247 (M.op (M.op X0 (M.op (M.op X2 X3) X1)) X1) X2 X3
       have i₂ := eq450 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq450 eq247
    | exact resolve eq247 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq450
  have eq699 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 (M.op X2 (M.op X3 X1))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq684 X0 X1 X2 X3
       have i₂ := eq538 X2 X3 X1 X0
       grind)
    | (have i₁ := eq684 X3 (M.op X1 X2) X2 X3
       have i₂ := eq538 (M.op X2 X3) X1 X2 X3
       grind)
    | exact superpose eq538 eq684
    | exact resolve eq684 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq740 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq699 X0 X1 X2 X3
       have i₂ := eq369 X1 X2 (M.op X3 X1) X0
       grind)
    | (have i₁ := eq699 X3 X2 X0 X3
       have i₂ := eq369 X0 (M.op X3 X2) X2 X3
       grind)
    | exact superpose eq369 eq699
    | exact resolve eq699 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq959 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X3) (M.op (M.op X1 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X3 (M.op X1 X1) X2
       have i₂ := eq547 X1 X2 X0
       grind)
    | exact superpose eq547 eq53
    | exact resolve eq53 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X2
       have i₂ := eq547 X1 X2 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq547 eq9
    | exact resolve eq9 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq455 (M.op X2 X2) X0 X1
       have i₂ := eq547 X2 X1 (M.op X0 X1)
       grind)
    | exact superpose eq547 eq455
    | exact resolve eq455 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq1013 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq959 X0 X2 X1 x
       have i₂ := eq290 X2 X2 X0 x
       grind)
    | exact superpose eq290 eq959
    | exact resolve eq959 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1396 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))) (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq576 X2 X1 (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0)))
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq576
    | exact resolve eq576 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1465 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op (M.op X1 X2) X0) X3 X2 X0
       have i₂ := eq576 X1 X2 X0
       grind)
    | exact superpose eq576 eq53
    | exact resolve eq53 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1501 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (M.op (σ X0) (σ (M.op X0 X0)))) (M.op X1 (σ X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1449 X0 X1 X2
       have i₂ := eq369 (σ X0) (σ (M.op X0 X0)) (M.op X1 (σ X0)) (M.op X2 X1)
       grind)
    | (have i₁ := eq1449 X0 X1 X2
       have i₂ := eq369 (σ (M.op X0 X0)) (M.op X1 (σ X0)) (σ X0) (M.op X2 X1)
       grind)
    | exact superpose eq369 eq1449
    | exact resolve eq1449 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1535 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (σ (M.op X0 X0))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1501 X0 X1 X2
       have i₂ := eq740 (M.op X2 X1) (σ X0) (σ (M.op X0 X0)) X1
       grind)
    | exact superpose eq740 eq1501
    | exact resolve eq1501 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq1501
  have eq1706 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq665 X2 X0 (M.op X1 X1)
       have i₂ := eq547 X1 X0 X0
       grind)
    | exact superpose eq547 eq665
    | exact resolve eq665 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq665
  have eq1835 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 (τ (M.op X0 X0))) X1) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq982 X2 (τ X0) X1
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq982
    | exact resolve eq982 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq982
  have eq2035 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op (M.op (M.op X1 X2) X0) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1013 (M.op (M.op X1 X2) X0) X3 (M.op X0 X2)
       have i₂ := eq576 X1 X2 X0
       grind)
    | exact superpose eq576 eq1013
    | exact resolve eq1013 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2037 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op (σ X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1013 (σ X0) X1 (σ X0)
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq1013
    | exact resolve eq1013 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq2244 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X1 X1))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0
       have i₂ := eq1706 X1 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq94 X0
       have i₂ := eq1706 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq1706 eq94
    | exact resolve eq94 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2664 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X1 (σ (M.op X3 X3))) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1535 X3 (M.op X0 X2) (M.op (M.op X1 X2) X0)
       have i₂ := eq576 X1 X2 X0
       grind)
    | exact superpose eq576 eq1535
    | exact resolve eq1535 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq2869 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (τ (M.op (M.op X0 X0) (M.op X1 X1)))) X3) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1835 (M.op X0 X0) X3 X2
       have i₂ := eq1706 X1 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq1835 (M.op X0 X0) X3 X2
       have i₂ := eq1706 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq1706 eq1835
    | exact resolve eq1835 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706 eq1835
  have eq3135 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) X3) = (M.op (M.op X1 (σ (M.op X4 X4))) (M.op (M.op X3 X2) (M.op X0 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1535 X4 (M.op (M.op X3 X2) (M.op X0 X2)) (M.op (M.op X1 X0) X3)
       have i₂ := eq54 X0 X3 X2 X1
       grind)
    | exact superpose eq54 eq1535
    | exact resolve eq1535 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1535
  have eq3136 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X3) = (M.op (M.op X1 (M.op X0 X2)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3135 X0 X1 X2 X3 x
       have i₂ := eq2664 (M.op X3 X2) X1 (M.op X0 X2) x
       grind)
    | exact superpose eq2664 eq3135
    | exact resolve eq3135 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq9340 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq1396 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq1396 X0 X1
       grind)
    | exact superpose eq1396 eq12
    | (have j1 := eq1396 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq1396 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq1396 X0 X1
       grind)
    | exact resolve eq12 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq9370 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9340
  have eq9386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9370 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9370
    | (have j0 := eq9370 X0 X1
       grind)
    | exact resolve eq9370 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9370
  have eq9387 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9386
  have eq11604 : ∀ X0 X1 : G, (τ X1) = (M.op (τ (M.op (M.op X1 X0) (M.op X0 X1))) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X1 X0
       have i₂ := eq654 X1 (M.op X0 X1) X0
       grind)
    | (have i₁ := eq248 X1 X0
       have i₂ := eq654 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq654 eq248
    | exact resolve eq248 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq18587 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (M.op (σ X0) X1) X1))) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11604 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq2037 X0 X1
       grind)
    | exact superpose eq2037 eq11604
    | exact resolve eq11604 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037 eq11604
  have eq18706 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (M.op (σ X0) X1) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18587 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18587
    | exact resolve eq18587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18587
  have eq18860 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op (σ X0) X1) (M.op (σ X0) X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18706 X0 X1
       have i₂ := eq2664 (M.op (σ X0) X1) (σ X0) X1 X0
       grind)
    | exact superpose eq2664 eq18706
    | exact resolve eq18706 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664 eq18706
  have eq26950 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9387 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9387
    | exact resolve eq9387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26967 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9387 y x
       grind)
    | exact superpose eq9387 eq16
    | (have j1 := eq9387 y x
       grind)
    | exact resolve eq16 eq9387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9387
  have eq27063 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26950 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq26950
    | (have j0 := eq26950 X0 X1
       grind)
    | exact resolve eq26950 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq26950
  have eq29596 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 (M.op X2 X1)) (M.op (M.op X0 X3) X1)) = (M.op (M.op X5 X4) (M.op (M.op (M.op X2 X0) X3) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq290 (M.op X2 X1) (M.op (M.op X0 X3) X1) X5 X4
       have i₂ := eq290 X0 X3 X2 X1
       grind)
    | exact superpose eq290 eq290
    | exact resolve eq290 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30122 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X5 (M.op X2 X1)) (M.op (M.op X0 X3) X1)) = (M.op (M.op X5 (M.op X2 X0)) X3) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq29596 X0 X1 X2 X3 x X5
       have i₂ := eq290 (M.op X2 X0) X3 X5 x
       grind)
    | exact superpose eq290 eq29596
    | exact resolve eq29596 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29596
  have eq30352 : ∀ X0 X2 X3 X5 : G, (M.op (M.op X5 (M.op X2 X0)) X3) = (M.op (M.op X5 X2) (M.op X0 X3)) := by
    intro X0 X2 X3 X5
    first
    | (have i₁ := eq30122 X0 x X2 X3 X5
       have i₂ := eq3136 X2 X5 x (M.op X0 X3)
       grind)
    | exact superpose eq3136 eq30122
    | exact resolve eq30122 eq3136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3136 eq30122
  have eq39919 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X2) X4) = (M.op (M.op (M.op X1 X0) X4) (M.op (M.op X0 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq654 (M.op X1 X0) X4 (M.op (M.op X0 X3) X2)
       have i₂ := eq368 X0 X3 X2 X1
       grind)
    | exact superpose eq368 eq654
    | exact resolve eq654 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq39962 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X2) X4) = (M.op (M.op (M.op X1 X0) X4) (M.op X0 (M.op X3 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq39919 X0 X1 X2 X3 X4
       have i₂ := eq538 X0 X3 X2 (M.op (M.op X1 X0) X4)
       grind)
    | (have i₁ := eq39919 X0 X1 (M.op X1 X2) X3 X4
       have i₂ := eq538 (M.op X0 X3) X1 X2 (M.op (M.op X1 X0) X4)
       grind)
    | exact superpose eq538 eq39919
    | exact resolve eq39919 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq39919
  have eq42571 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X0 X3)) X2) X4) = (M.op (M.op (M.op X1 (M.op X3 X2)) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq654 (M.op X1 (M.op X3 X2)) X4 X0
       have i₂ := eq369 X0 X3 X2 X1
       grind)
    | (have i₁ := eq654 (M.op X3 (M.op X0 X1)) X1 X2
       have i₂ := eq369 X0 X1 X2 X3
       grind)
    | exact superpose eq369 eq654
    | exact resolve eq654 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq42797 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X0 X3)) X2) X4) = (M.op (M.op (M.op X1 X3) (M.op X2 X4)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42571 X0 X1 X2 X3 X4
       have i₂ := eq30352 X2 X3 X4 X1
       grind)
    | exact superpose eq30352 eq42571
    | exact resolve eq42571 eq30352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42571
  have eq43300 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X0 X3)) X2) X4) = (M.op (M.op (M.op X1 X3) X2) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42797 X0 X1 X2 X3 X4
       have i₂ := eq30352 X4 X2 X0 (M.op X1 X3)
       grind)
    | exact superpose eq30352 eq42797
    | exact resolve eq42797 eq30352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42797
  have eq43664 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X2) (M.op X4 X0)) = (M.op (M.op (M.op X1 X0) (M.op X3 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq43300 X0 X1 X2 X3 X4
       have i₂ := eq30352 X3 X0 X2 X1
       grind)
    | exact superpose eq30352 eq43300
    | exact resolve eq43300 eq30352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43300
  have eq43904 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X2) (M.op X4 X0)) = (M.op (M.op (M.op X1 X0) X3) (M.op X2 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq43664 X0 X1 X2 X3 X4
       have i₂ := eq30352 X2 X3 X4 (M.op X1 X0)
       grind)
    | exact superpose eq30352 eq43664
    | exact resolve eq43664 eq30352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43664
  have eq45527 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq27063 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27063
    | exact resolve eq27063 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27063
  have eq45558 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq45527 (τ X0) X1
       grind)
    | exact superpose eq45527 eq18
    | (have j1 := eq45527 (τ X0) X1
       grind)
    | exact resolve eq18 eq45527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45527
  have eq263379 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45558 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45558
    | exact resolve eq45558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45558
  have eq263565 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq263379 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq263379
    | (have j0 := eq263379 X0 X1
       grind)
    | exact resolve eq263379 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263379
  have eq382399 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 (τ (M.op (M.op (M.op X2 X1) X2) (M.op X1 (M.op X0 X0))))) X3) X3) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2869 (M.op X2 X1) X0 X4 X3
       have i₂ := eq30352 X1 X2 (M.op X0 X0) (M.op X2 X1)
       grind)
    | exact superpose eq30352 eq2869
    | exact resolve eq2869 eq30352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2869 eq30352
  have eq383542 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X4 (τ (M.op (M.op (M.op X2 X0) X0) X2))) X3) X3) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq382399 X0 x X2 X3 X4
       have i₂ := eq39962 x X2 X0 X0 X2
       grind)
    | exact superpose eq39962 eq382399
    | exact resolve eq382399 eq39962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39962 eq382399
  have eq640559 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26967
       have i₂ := eq263565 x y
       grind)
    | exact superpose eq263565 eq26967
    | (have j1 := eq263565 (σ x) (σ y)
       grind)
    | (have r₁ := eq26967
       have r₂ := eq263565 x y
       grind)
    | exact resolve eq26967 eq263565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26967 eq263565
  have eq640560 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq640559
  have eq644935 : x = (M.op (τ (M.op (σ y) (σ y))) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18860 x (σ y)
       have i₂ := eq640560
       grind)
    | exact superpose eq640560 eq18860
    | exact resolve eq18860 eq640560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18860
  have eq644988 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 (σ x)) X0) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1465 X0 X1 (σ x) (σ y)
       have i₂ := eq640560
       grind)
    | exact superpose eq640560 eq1465
    | exact resolve eq1465 eq640560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465 eq640560
  have eq645302 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (σ x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq644988 X0 X1
       have i₂ := eq2035 X0 X1 (σ x) (σ y)
       grind)
    | exact superpose eq2035 eq644988
    | exact resolve eq644988 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq644988
  have eq645319 : x = (M.op (τ (σ (M.op y y))) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq644935
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq644935
    | exact resolve eq644935 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq644935
  have eq645367 : x = (M.op (M.op y y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq645319
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq645319
    | exact resolve eq645319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645319
  have eq645373 : x = (M.op (M.op y x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq645367
       have i₂ := eq654 y y x
       grind)
    | (have i₁ := eq645367
       have i₂ := eq654 y x y
       grind)
    | exact superpose eq654 eq645367
    | exact resolve eq645367 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq645367
  have eq646287 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (M.op X0 (σ x))) (M.op X1 X0)) = X2 ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq263 X2 X1 (M.op X0 (σ x))
       have i₂ := eq645302 X0 X1
       grind)
    | exact superpose eq645302 eq263
    | exact resolve eq263 eq645302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq645302
  have eq646693 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) X1) (M.op (M.op X0 (σ x)) X1)) = X2 ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646287 X0 X1 X2
       have i₂ := eq43904 X0 X2 (M.op X0 (σ x)) X1 X1
       grind)
    | (have i₁ := eq646287 x X2 X1
       have i₂ := eq43904 X2 X1 X2 (M.op x (σ x)) x
       grind)
    | exact superpose eq43904 eq646287
    | exact resolve eq646287 eq43904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43904 eq646287
  have eq646927 : ∀ X0 X2 : G, (M.op (M.op (M.op X2 X0) X0) (σ x)) = X2 ∨ y = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq646693 X0 x X2
       have i₂ := eq290 X0 (σ x) (M.op X2 X0) x
       grind)
    | exact superpose eq290 eq646693
    | exact resolve eq646693 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq646693
  have eq653877 : ∀ X1 X2 : G, (M.op (M.op (M.op X1 (τ (σ x))) X2) X2) = X1 ∨ y = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq383542 x (σ x) X2 X1
       have i₂ := eq646927 x (σ x)
       grind)
    | exact superpose eq646927 eq383542
    | exact resolve eq383542 eq646927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383542 eq646927
  have eq654112 : ∀ X1 X2 : G, (M.op (M.op (M.op X1 x) X2) X2) = X1 ∨ y = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq653877 X1 X2
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq653877
    | exact resolve eq653877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653877
  have eq660091 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq654112 y y
       have i₂ := eq645373
       grind)
    | exact superpose eq645373 eq654112
    | exact resolve eq654112 eq645373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645373 eq654112
  have eq660720 : y = (M.op x y) := by grind
  clear eq660091
  have eq669356 : ∀ X0 : G, x = (M.op (M.op y y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq983 x y X0
       have i₂ := eq660720
       grind)
    | exact superpose eq660720 eq983
    | exact resolve eq983 eq660720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq676929 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2244 y x
       have i₂ := eq669356 x
       grind)
    | exact superpose eq669356 eq2244
    | exact resolve eq2244 eq669356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244 eq669356
  have eq678100 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq676929
       grind)
    | exact superpose eq676929 eq16
    | exact resolve eq16 eq676929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676929
  have eq678400 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq678100
       have i₂ := eq660720
       grind)
    | exact superpose eq660720 eq678100
    | exact resolve eq678100 eq660720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660720 eq678100
  have eq678401 : False := by grind
  exact eq678401

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxx_pyx_pxy_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
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
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
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
  clear eq43
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq90 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq106 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq110 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq106
    | exact resolve eq106 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq112 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq110
    | exact resolve eq110 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq138 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq135
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq135
    | exact resolve eq135 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq138
    | exact resolve eq138 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq147 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq16
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq181 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 X1) (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op (M.op x y) (M.op X1 y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 x) X0) (M.op (M.op X0 y) (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq34
    | exact resolve eq34 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq303 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq292
    | exact resolve eq292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq305 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq303 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq303
    | exact resolve eq303 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq303
  have eq432 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X4 X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 (M.op X2 (M.op (M.op x y) (M.op X1 y)))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (σ x) X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4) (M.op X3 X4)) = (M.op X0 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4 X3 X2
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 X1) y)) X2) (M.op X1 X2)) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) X2 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 x X2
       have i₂ := eq52 X0 x X2 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) (M.op X0 X4)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X3 (M.op X2 X4) (M.op X0 X4)
       have i₂ := eq52 X0 X4 X2 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x y) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op y X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op X0 (M.op y X2))
       have i₂ := eq52 X0 X1 X2 y
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) (M.op (M.op X2 X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (M.op X0 X1) (M.op X2 X1) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 X1) (M.op (M.op X0 y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X1) (M.op (M.op X0 (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) (M.op (σ x) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) (M.op X0 (M.op X5 X2))) (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X4 X5))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X0 (M.op X5 X2)) X3 X4 X5
       have i₂ := eq52 X0 X1 X2 X5
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) (M.op X0 (M.op X2 (σ x)))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) X2) (M.op (M.op X2 (σ x)) X0)) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X3 X2 x
       have i₂ := eq52 X0 x X2 X1
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq55 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X5 (M.op (M.op X0 X4) X2))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X1 (M.op (M.op X2 X3) (M.op X4 X3)) (M.op (M.op X0 X4) X2) X5
       have i₂ := eq55 X2 X0 X4 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq55
  have eq814 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq16
    | exact resolve eq16 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq248 eq458
    | exact resolve eq458 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq458 (M.op X0 X1) X2 (M.op X1 X2)
       have i₂ := eq458 X0 X1 X2
       grind)
    | exact superpose eq458 eq458
    | exact resolve eq458 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq458 (M.op X0 X1) (M.op X2 X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq458
    | exact resolve eq458 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq458
    | exact resolve eq458 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq458
    | exact resolve eq458 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1175 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq53 eq458
    | exact resolve eq458 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq54 eq458
    | exact resolve eq458 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1210 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq458
    | (have j0 := eq458 X0 (σ x) (σ y)
       grind)
    | exact resolve eq458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1416 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq248 eq563
    | exact resolve eq563 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq1420 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq563 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq563
    | (have j0 := eq563 X0 x y
       grind)
    | exact resolve eq563 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1424 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq563
    | (have j0 := eq563 X0 (σ x) (σ y)
       grind)
    | exact resolve eq563 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1428 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq462 X0 X2 X2
       grind)
    | exact superpose eq462 eq563
    | exact resolve eq563 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1432 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq563 (M.op (M.op X0 (M.op X1 X2)) X2) X1 X2
       have i₂ := eq458 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq458 eq563
    | exact resolve eq563 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1473 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op x y)
       have i₂ := eq563 sF0 x y
       grind)
    | exact superpose eq563 eq50
    | exact resolve eq50 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1478 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op x sF3)
       have i₂ := eq563 sF4 x sF3
       grind)
    | exact superpose eq563 eq51
    | exact resolve eq51 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1821 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) (M.op (M.op (M.op X0 X1) (M.op y X1)) y))) := by
    intro X0 X1
    first
    | exact superpose eq237 eq241
    | exact resolve eq241 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq241
  have eq1902 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1821 X0 x
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq1821
    | exact resolve eq1821 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq2052 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) y) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1420 (M.op (M.op X0 sF0) y)
       have i₂ := eq458 X0 sF0 y
       grind)
    | exact superpose eq458 eq1420
    | exact resolve eq1420 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2095 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq1420 eq50
    | exact resolve eq50 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1420
  have eq2270 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2095 eq563
    | exact resolve eq563 eq2095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095
  have eq2271 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1175 eq2270
    | exact resolve eq2270 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq2270
  have eq2471 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1424 eq51
    | exact resolve eq51 eq1424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq2502 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2471 eq458
    | exact resolve eq458 eq2471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq2689 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x X0) y) := by
    intro X0
    first
    | exact superpose eq1473 eq462
    | exact resolve eq462 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3484 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | exact superpose eq2052 eq458
    | exact resolve eq458 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq4443 : x = (M.op (M.op (M.op x y) y) (M.op (M.op x (M.op x y)) y)) := by
    first
    | exact superpose eq2271 eq1473
    | exact resolve eq1473 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271
  have eq4463 : x = (M.op (M.op (M.op x y) y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq4443
       have i₂ := eq2689 sF0
       grind)
    | exact superpose eq2689 eq4443
    | exact resolve eq4443 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq6590 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq4463 eq462
    | exact resolve eq462 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4463
  have eq8552 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 X0) y)) := by
    intro X0
    first
    | (have i₁ := eq522 X0 X0
       have i₂ := eq1169 (M.op X0 X0) y X0
       grind)
    | exact superpose eq1169 eq522
    | exact resolve eq522 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq8553 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq523 x x
       have i₂ := eq1169 (M.op x x) sF3 x
       grind)
    | exact superpose eq1169 eq523
    | exact resolve eq523 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9558 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq462 x (M.op X0 X0) y
       have i₂ := eq8552 X0
       grind)
    | exact superpose eq8552 eq462
    | exact resolve eq462 eq8552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8552
  have eq9657 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq8553 eq462
    | exact resolve eq462 eq8553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8553
  have eq12278 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1170 (M.op (M.op y (M.op X0 X0)) X0)
       have i₂ := eq559 y X0 X0 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq559 eq1170
    | exact resolve eq1170 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq12279 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1171 (M.op (M.op sF3 (M.op x x)) x)
       have i₂ := eq559 sF3 x x (M.op sF3 (M.op x x))
       grind)
    | exact superpose eq559 eq1171
    | exact resolve eq1171 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1171
  have eq12538 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12278 (τ X0)
       have i₂ := eq814 X0
       grind)
    | exact superpose eq814 eq12278
    | exact resolve eq12278 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12547 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq462 x y (M.op X0 X0)
       have i₂ := eq12278 X0
       grind)
    | exact superpose eq12278 eq462
    | exact resolve eq462 eq12278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12278
  have eq12639 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq12279 eq462
    | exact resolve eq462 eq12279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq12279
  have eq12720 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12547 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq12547
    | exact resolve eq12547 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12547
  have eq12834 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12639 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq12639
    | exact resolve eq12639 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq12836 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12639 (τ X0)
       have i₂ := eq814 X0
       grind)
    | exact superpose eq814 eq12639
    | exact resolve eq12639 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq12639
  have eq18450 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq452 eq523
    | exact resolve eq523 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq523
  have eq19399 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 y) y)) (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq455 eq263
    | exact resolve eq263 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq19506 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq19399 x
       have i₂ := eq563 sF0 x y
       grind)
    | exact superpose eq563 eq19399
    | exact resolve eq19399 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19399
  have eq22455 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 x) (M.op y (M.op (M.op x y) y)))) := by
    intro X0
    first
    | exact superpose eq268 eq476
    | exact resolve eq476 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq476
  have eq22673 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq22455 X0
       have i₂ := eq1168 (M.op X0 x) sF0 y
       grind)
    | exact superpose eq1168 eq22455
    | exact resolve eq22455 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22455
  have eq23562 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1432 (M.op (M.op X0 X2) X1) X2 X1
       have i₂ := eq458 X0 X2 X1
       grind)
    | exact superpose eq458 eq1432
    | exact resolve eq1432 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq1432
  have eq28082 : ∀ X0 : G, (M.op (M.op x x) X0) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1902 (M.op x sF0)
       have i₂ := eq1168 (M.op x x) x sF0
       grind)
    | exact superpose eq1168 eq1902
    | exact resolve eq1902 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq32338 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq537
    | exact resolve eq537 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq32357 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op X1 (σ x)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq537
    | (have j0 := eq537 X0 X1 (σ x)
       grind)
    | exact resolve eq537 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq32844 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32357 X0 X1
       have i₂ := eq1168 (M.op (M.op X0 X1) (M.op sF4 sF4)) X1 sF2
       grind)
    | exact superpose eq1168 eq32357
    | exact resolve eq32357 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32357
  have eq32851 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32338 X0 X1
       have i₂ := eq1428 sF4 X1 sF3
       grind)
    | exact superpose eq1428 eq32338
    | exact resolve eq32338 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428 eq32338
  have eq32921 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1416 eq32844
    | exact resolve eq32844 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq32844
  have eq32925 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ y)) (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1181 eq32851
    | exact resolve eq32851 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq32851
  have eq38309 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op (M.op (M.op y (σ x)) (σ y)) (M.op (σ x) (σ y)))) X0) (M.op (M.op X0 (M.op x y)) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq556 (M.op y sF2) X1 X0
       have i₂ := eq263 X0 sF2
       grind)
    | exact superpose eq263 eq556
    | exact resolve eq556 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq556
  have eq38530 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 y) X0) (M.op (M.op X0 (M.op x y)) x)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1210 eq38309
    | exact resolve eq38309 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210 eq38309
  have eq39305 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq542 eq432
    | exact resolve eq432 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq542
  have eq57326 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq520 X2 (M.op X0 X1) X1 x x
       have i₂ := eq454 X1 x X0 X1 x
       grind)
    | exact superpose eq454 eq520
    | exact resolve eq520 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq111501 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) (M.op X3 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq467 (M.op X2 X2) (M.op X1 X3) X2 (M.op X0 X1) (M.op X3 (M.op X1 X3))
       have i₂ := eq538 X2 X2 (M.op X1 X3) X0 X1 X3
       grind)
    | exact superpose eq538 eq467
    | exact resolve eq467 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq538
  have eq111808 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111501 X0 X1 X2 x
       have i₂ := eq1168 (M.op X2 X2) X1 x
       grind)
    | exact superpose eq1168 eq111501
    | exact resolve eq111501 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111501
  have eq131611 : ∀ X0 X2 X3 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op X2 y) (M.op x y)))) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq459 eq571
    | exact resolve eq571 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq131614 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (σ x)) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op X2 (σ y)) (M.op (σ x) (σ y))))) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq460 eq571
    | exact resolve eq571 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq571
  have eq134974 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (σ x)) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y))))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq131614 X0 X2 X2
       have i₂ := eq57326 (M.op X2 sF3) sF4 X2
       grind)
    | (have i₁ := eq131614 X0 X2 X2
       have i₂ := eq57326 sF4 (M.op X2 sF3) X2
       grind)
    | exact superpose eq57326 eq131614
    | exact resolve eq131614 eq57326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131614
  have eq134977 : ∀ X0 X2 X3 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op x y) (M.op X2 y)))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq131611 X0 X2 X2
       have i₂ := eq57326 (M.op X2 y) sF0 X2
       grind)
    | (have i₁ := eq131611 X0 X2 X2
       have i₂ := eq57326 sF0 (M.op X2 y) X2
       grind)
    | exact superpose eq57326 eq131611
    | exact resolve eq131611 eq57326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131611
  have eq135893 : ∀ X0 X2 : G, (M.op (M.op X0 X2) (σ x)) = (M.op (M.op X0 (σ x)) X2) := by
    intro X0 X2
    first
    | exact superpose eq439 eq134974
    | exact resolve eq134974 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq134974
  have eq135896 : ∀ X0 X2 : G, (M.op (M.op X0 X2) x) = (M.op (M.op X0 x) X2) := by
    intro X0 X2
    first
    | exact superpose eq438 eq134977
    | exact resolve eq134977 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq134977
  have eq226718 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq226734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq226718
    | exact resolve eq226718 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226718
  have eq226741 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq226734
       have r₂ := eq27
       grind)
    | exact resolve eq226734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226734
  have eq226743 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq226741
    | exact resolve eq226741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226741
  have eq226745 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq226743
    | exact resolve eq226743 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226743
  have eq226983 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq226745 eq32921
    | exact resolve eq32921 eq226745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226745
  have eq227015 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9657 eq226983
    | exact resolve eq226983 eq9657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9657 eq226983
  have eq227564 : y = (M.op (M.op (M.op x y) (M.op (σ x) (σ x))) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32921 y y
       have i₂ := eq227015
       grind)
    | exact superpose eq227015 eq32921
    | exact resolve eq32921 eq227015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32921 eq227015
  have eq227595 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9558 eq227564
    | exact resolve eq227564 eq9558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9558 eq227564
  have eq227958 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq227595 eq1478
    | exact resolve eq1478 eq227595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq227963 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq227595 eq2502
    | exact resolve eq2502 eq227595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq228040 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq227963
    | exact resolve eq227963 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq227963
  have eq230955 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq228040 eq1158
    | exact resolve eq1158 eq228040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228040
  have eq372152 : (M.op x y) = (M.op x (M.op y (τ (σ x)))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f372152_14 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (τ (M.op X0 X0)))) := by
      intro X0
      grind
    have f372152_15 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f372152_23 : (M.op x y) ≠ (M.op x (M.op y (τ (σ x)))) := by grind
    have f372152_24 : x ≠ y := by grind
    have f372152_25 : y ≠ (M.op x y) := by grind
    have f372152_26 : (σ x) ≠ (σ y) := by grind
    have f372152_27 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
      intro X0
      first
      | (have j0 := f372152_15 X0
         grind)
      | (have r₁ := f372152_15 X0
         have r₂ := f372152_24
         grind)
      | exact resolve f372152_15 f372152_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f372152_28 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) ∨ (σ x) = (σ y) := by
      intro X0
      first
      | (have j0 := f372152_27 X0
         grind)
      | (have r₁ := f372152_27 X0
         have r₂ := f372152_25
         grind)
      | exact resolve f372152_27 f372152_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f372152_29 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) := by
      intro X0
      first
      | (have j0 := f372152_28 X0
         grind)
      | (have r₁ := f372152_28 X0
         have r₂ := f372152_26
         grind)
      | exact resolve f372152_28 f372152_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f372152_53 : (M.op x y) = (M.op x (M.op y (τ (σ x)))) := by
      first
      | (have i₁ := f372152_14 (M.op (σ y) (σ y))
         have i₂ := f372152_29 (σ y)
         grind)
      | exact superpose f372152_29 f372152_14
      | exact resolve f372152_14 f372152_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f372152_54 : False := by
      first
      | (have r₁ := f372152_53
         have r₂ := f372152_23
         grind)
      | exact resolve f372152_53 f372152_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f372152_54
  clear eq12538
  have eq372160 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (τ (σ x))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq227958 eq12836
    | exact resolve eq12836 eq227958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12836 eq227958
  have eq372614 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28 eq372160
    | exact resolve eq372160 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372160
  have eq372618 : (M.op x y) = (M.op x (M.op y x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28 eq372152
    | exact resolve eq372152 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372152
  have eq372933 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq372614
       have i₂ := eq135896 sF4 sF3
       grind)
    | exact superpose eq135896 eq372614
    | exact resolve eq372614 eq135896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135896 eq372614
  have eq372936 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq372618
       have i₂ := eq3484 x
       grind)
    | exact superpose eq3484 eq372618
    | exact resolve eq372618 eq3484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484 eq372618
  have eq373826 : (σ x) = (M.op (M.op (σ y) x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq227595 eq372933
    | exact resolve eq372933 eq227595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227595 eq372933
  have eq374087 : (σ x) = (M.op (M.op (σ y) x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq373826
  have eq378425 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq374087 eq1169
    | exact resolve eq1169 eq374087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq374087
  have eq380679 : (M.op x x) = (τ (M.op (σ x) x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq378425 eq71
    | exact resolve eq71 eq378425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378425
  have eq397421 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) x) (M.op (σ x) x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq380679 eq305
    | exact resolve eq305 eq380679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380679
  have eq397464 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x x))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1158 eq397421
    | exact resolve eq397421 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397421
  have eq397473 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op (M.op x x) (M.op x y)))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq397464
       have i₂ := eq28082 (M.op x x)
       grind)
    | exact superpose eq28082 eq397464
    | exact resolve eq397464 eq28082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397464
  have eq397478 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq397473
       have i₂ := eq111808 sF0 sF0 x
       grind)
    | exact superpose eq111808 eq397473
    | exact resolve eq397473 eq111808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397473
  have eq397480 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq140 eq397478
    | exact resolve eq397478 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397478
  have eq397499 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq397480 eq230955
    | exact resolve eq230955 eq397480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230955 eq397480
  have eq397774 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq397499
  have eq400056 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq397774 eq147
    | exact resolve eq147 eq397774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq397774
  have eq400552 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq181 eq400056
    | exact resolve eq400056 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq400056
  have eq402040 : (M.op x (M.op x y)) = (M.op (M.op (M.op y y) (M.op x y)) x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq400552 eq19506
    | exact resolve eq19506 eq400552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19506 eq400552
  have eq402478 : y = (M.op x (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq53 eq402040
    | exact resolve eq402040 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq402040
  have eq402724 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq402478 eq372936
    | exact resolve eq372936 eq402478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372936 eq402478
  have eq402956 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq402724
  have eq403257 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq402956 eq29
    | exact resolve eq29 eq402956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq402956
  have eq403443 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq403257
    | exact resolve eq403257 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq403257
  have eq403444 : y = (M.op x y) ∨ x = y := by grind
  clear eq403443
  have eq403466 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq403444 eq20
    | exact resolve eq20 eq403444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403568 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op X0 y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq403444 eq1473
    | exact resolve eq1473 eq403444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq403593 : (M.op y y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq403444 eq6590
    | exact resolve eq6590 eq403444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590 eq403444
  have eq403649 : (M.op y y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq403593
       have i₂ := eq2689 y
       grind)
    | exact superpose eq2689 eq403593
    | exact resolve eq403593 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689 eq403593
  have eq403760 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq403466
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq403466
    | exact resolve eq403466 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403466
  have eq405964 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op (M.op y y) (M.op (M.op X0 X1) y)) X2) (M.op X1 X2)) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq403649 eq454
    | exact resolve eq454 eq403649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403649
  have eq406267 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq405964 X0 x x
       have i₂ := eq454 y y X0 x x
       grind)
    | exact superpose eq454 eq405964
    | exact resolve eq405964 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq405964
  have eq440572 : x = (M.op (M.op (M.op x y) y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq12720 (M.op y y)
       have i₂ := eq403568 y
       grind)
    | exact superpose eq403568 eq12720
    | exact resolve eq12720 eq403568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12720
  have eq440574 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq12834 (M.op y y)
       have i₂ := eq403568 y
       grind)
    | exact superpose eq403568 eq12834
    | exact resolve eq12834 eq403568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12834 eq403568
  have eq441002 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq440574
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq440574
    | exact resolve eq440574 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440574
  have eq441003 : x = (M.op (M.op (M.op x y) y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq440572
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq440572
    | exact resolve eq440572 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440572
  have eq441337 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq135893 eq441002
    | exact resolve eq441002 eq135893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135893 eq441002
  have eq442265 : x = (M.op (M.op y y) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq406267 eq441003
    | exact resolve eq441003 eq406267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406267 eq441003
  have eq442517 : x = (M.op (M.op y y) (σ x)) ∨ x = y := by grind
  clear eq442265
  have eq443864 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq403760 eq441337
    | exact resolve eq441337 eq403760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403760 eq441337
  have eq444132 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq443864
  have eq444364 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq444132
       have i₂ := eq23562 sF4 sF2 sF1
       grind)
    | (have i₁ := eq444132
       have i₂ := eq23562 sF4 sF1 sF2
       grind)
    | exact superpose eq23562 eq444132
    | exact resolve eq444132 eq23562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23562 eq444132
  have eq453623 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq442517 eq111808
    | exact resolve eq111808 eq442517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442517
  have eq462490 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq444364 eq521
    | exact resolve eq521 eq444364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq444364
  have eq462940 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq462490 X0
       have i₂ := eq563 X0 sF4 sF2
       grind)
    | exact superpose eq563 eq462490
    | exact resolve eq462490 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462490
  have eq464582 : (M.op x x) = (τ (M.op (σ x) x)) ∨ x = y := by
    first
    | exact superpose eq453623 eq71
    | exact resolve eq71 eq453623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453623
  have eq494473 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) x) (M.op (σ x) x)) ∨ x = y := by
    first
    | exact superpose eq464582 eq305
    | exact resolve eq305 eq464582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq464582
  have eq494516 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x x))) ∨ x = y := by
    first
    | exact superpose eq1158 eq494473
    | exact resolve eq494473 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq494473
  have eq494525 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op (M.op x x) (M.op x y)))) ∨ x = y := by
    first
    | (have i₁ := eq494516
       have i₂ := eq28082 (M.op x x)
       grind)
    | exact superpose eq28082 eq494516
    | exact resolve eq494516 eq28082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28082 eq494516
  have eq494530 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq494525
       have i₂ := eq111808 sF0 sF0 x
       grind)
    | exact superpose eq111808 eq494525
    | exact resolve eq494525 eq111808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111808 eq494525
  have eq494532 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq140 eq494530
    | exact resolve eq494530 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq494530
  have eq494588 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq494532 eq462940
    | exact resolve eq462940 eq494532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462940 eq494532
  have eq494833 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq494588
  have eq496056 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq494833 eq32925
    | exact resolve eq32925 eq494833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494833
  have eq496099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq32925 eq496056
    | exact resolve eq496056 eq32925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32925 eq496056
  have eq496285 : x = y := by
    first
    | (have r₁ := eq496099
       have r₂ := eq27
       grind)
    | exact resolve eq496099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496099
  have eq496440 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq496285
       grind)
    | exact superpose eq496285 eq24
    | exact resolve eq24 eq496285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq496743 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq496440
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq496440
    | exact resolve eq496440 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq496440
  have eq496799 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 y) X0) (M.op x (M.op X0 (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38530 X0 X1
       have i₂ := eq57326 (M.op X0 sF0) x (M.op (M.op X1 y) X0)
       grind)
    | (have i₁ := eq38530 X0 X1
       have i₂ := eq57326 x (M.op X0 sF0) (M.op (M.op X1 y) X0)
       grind)
    | exact superpose eq57326 eq38530
    | exact resolve eq38530 eq57326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38530 eq57326
  have eq496800 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 x) X0) (M.op x (M.op X0 (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq496799 X0 X1
       have i₂ := eq496285
       grind)
    | exact superpose eq496285 eq496799
    | exact resolve eq496799 eq496285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496285 eq496799
  have eq496953 : (M.op x y) = (M.op x (M.op x (M.op (M.op (M.op x x) (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq22673 eq496800
    | exact resolve eq496800 eq22673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22673 eq496800
  have eq497921 : (M.op x y) = (M.op x (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq496953
       have i₂ := eq563 x (M.op x x) sF0
       grind)
    | exact superpose eq563 eq496953
    | exact resolve eq496953 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq496953
  have eq498263 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq497921
       have i₂ := eq1168 x x x
       grind)
    | exact superpose eq1168 eq497921
    | exact resolve eq497921 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq497921
  have eq502517 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq496743 eq39305
    | exact resolve eq39305 eq496743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39305 eq496743
  have eq502763 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18450 eq502517
    | exact resolve eq502517 eq18450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18450 eq502517
  have eq505261 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq502763 eq71
    | exact resolve eq71 eq502763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq502763
  have eq505785 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq505261
       have i₂ := eq498263
       grind)
    | exact superpose eq498263 eq505261
    | exact resolve eq505261 eq498263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498263 eq505261
  have eq506061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq505785 eq15
    | exact resolve eq15 eq505785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505785
  have eq506138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq506061
    | exact resolve eq506061 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq506061
  have eq506160 : False := by grind
  exact eq506160

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pxy_pyy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 y x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq78 : x = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq52 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : x = (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op y y))) := by
    first
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op X0 (M.op X1 x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ x)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : x ≠ x ∨ (M.op x (M.op (M.op x y) (M.op x y))) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq78 eq12
    | (have j0 := eq12 x (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq12 x (M.op (M.op x y) (M.op x y))
       have r₂ := eq78
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq115 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       have r₂ := eq93
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by grind
  clear eq115
  have eq118 : (M.op x (M.op (M.op x y) (M.op x y))) = (k x (M.op (M.op x y) (M.op x y))) := by grind
  clear eq112
  have eq125 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq125 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq125 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq125 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq134 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq126 (σ X0)
       grind)
    | exact superpose eq126 eq15
    | exact resolve eq15 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq134 X0
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq134
    | exact resolve eq134 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq134
  have eq151 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq193 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq10
    | exact resolve eq10 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq151
    | exact resolve eq151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq236 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq193 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq193
    | exact resolve eq193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq353 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq357 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq353
    | exact resolve eq353 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq359 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq357
    | exact resolve eq357 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq361 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq359
    | exact resolve eq359 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq370 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X5 (M.op X0 X4))) X5) = (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X3 (M.op X2 X4) (M.op X0 X4) X5
       have i₂ := eq53 X0 X4 X2 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) (M.op y y)) X1)) = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op y y) X0)) := by
    intro X0
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 X3) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 x
       have i₂ := eq53 X0 X3 X2 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x
       have i₂ := eq53 sF0 x y x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq57 x
       have i₂ := eq53 sF4 x sF3 x
       grind)
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq53 (M.op X0 X1) X2 X1 x
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op (σ y) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op X0 (M.op sF3 X2))
       have i₂ := eq53 X0 X1 X2 sF3
       grind)
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq399 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq399
    | (have j0 := eq399 X0 x y
       grind)
    | exact resolve eq399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq399
    | (have j0 := eq399 X0 (σ x) (σ y)
       grind)
    | exact resolve eq399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq399 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) X2 X3
       have i₂ := eq399 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq399 eq399
    | exact resolve eq399 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X0 X1) y)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq399
    | exact resolve eq399 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (σ y))) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq399
    | exact resolve eq399 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2
       have i₂ := eq399 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq399 eq9
    | exact resolve eq9 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 (M.op y sF0))
       have i₂ := eq399 X0 y sF0
       grind)
    | exact superpose eq399 eq54
    | exact resolve eq54 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op sF3 sF4))
       have i₂ := eq399 X0 sF3 sF4
       grind)
    | exact superpose eq399 eq56
    | exact resolve eq56 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op X1 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq399 X0 X1 y
       grind)
    | exact superpose eq399 eq54
    | exact resolve eq54 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op X1 y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq399 X0 X1 y
       grind)
    | exact superpose eq399 eq52
    | exact resolve eq52 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq546 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op X1 (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq399 X0 X1 sF3
       grind)
    | exact superpose eq399 eq57
    | exact resolve eq57 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq547 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (M.op X1 (σ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq399 X0 X1 sF3
       grind)
    | exact superpose eq399 eq56
    | exact resolve eq56 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq549 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq547 eq546
    | (have j0 := eq546 X0 (σ x)
       grind)
    | exact resolve eq546 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq547
  have eq551 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq545 X0 x
       have i₂ := eq544 X0 x
       grind)
    | (have i₁ := eq545 X0 x
       have i₂ := eq544 X0 x
       grind)
    | exact superpose eq544 eq545
    | (have j0 := eq545 X0 x
       grind)
    | exact resolve eq545 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq562 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) = (M.op (M.op X3 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq370 X0 X1 X2 X3 X4 x
       have i₂ := eq517 X3 x X0 X4
       grind)
    | exact superpose eq517 eq370
    | exact resolve eq370 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq572 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq492 (M.op X0 (M.op sF0 x))
       have i₂ := eq399 X0 sF0 x
       grind)
    | exact superpose eq399 eq492
    | exact resolve eq492 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq580 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) (M.op y y)) X1)) = (M.op (M.op X0 x) y) := by
    intro X0 X1
    first
    | exact superpose eq572 eq379
    | exact resolve eq379 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq572
  have eq614 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq535 eq399
    | exact resolve eq399 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq536 eq399
    | exact resolve eq399 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq810 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op (M.op X4 X5) (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op (M.op X0 X1) X2) (M.op (M.op X2 X3) (M.op X1 X3)) X5
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (M.op X0 (M.op X1 X2)) X1 X3
       have i₂ := eq399 X0 X1 X2
       grind)
    | exact superpose eq399 eq55
    | exact resolve eq55 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) (M.op (M.op X2 X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (M.op X0 X1) (M.op X2 X1) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq55 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq399 (M.op (M.op X0 X1) X2) (M.op X2 X3) (M.op X1 X3)
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq399
    | exact resolve eq399 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op (M.op X1 X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X2) X3 (M.op X1 X4) (M.op X2 X4)
       have i₂ := eq55 X2 X0 X1 X4
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X5 X4)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X2) (M.op (M.op X2 X3) (M.op X1 X3)) X4 X5
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X5 (M.op (M.op X0 X4) X2))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X1 (M.op (M.op X2 X3) (M.op X4 X3)) (M.op (M.op X0 X4) X2) X5
       have i₂ := eq55 X2 X0 X4 X3
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq931 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X0 X4)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq928 X0 X1 X2 X3 X4 x
       have i₂ := eq517 X1 x (M.op X0 X4) X2
       grind)
    | exact superpose eq517 eq928
    | exact resolve eq928 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1057 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) (M.op (M.op (M.op x y) (M.op y y)) X0)) := by
    intro X0
    first
    | exact superpose eq80 eq409
    | exact resolve eq409 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1146 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X4 X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3 X4
       have i₂ := eq409 X0 X1 X2
       grind)
    | exact superpose eq409 eq53
    | exact resolve eq53 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1160 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op X0 (M.op X4 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq927 X0 X1 X2 X3 X4 x
       have i₂ := eq1146 X0 X1 X2 X4 x
       grind)
    | exact superpose eq1146 eq927
    | exact resolve eq927 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq1195 : (M.op (M.op x y) x) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq580 eq1057
    | exact resolve eq1057 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq1057
  have eq1225 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) x)) (M.op x x)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq399 X0 (M.op x x) y
       have i₂ := eq1195
       grind)
    | exact superpose eq1195 eq399
    | exact resolve eq399 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1229 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1225 X0
       have i₂ := eq918 X0 x sF0 x
       grind)
    | exact superpose eq918 eq1225
    | exact resolve eq1225 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq1225
  have eq1292 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1229 (M.op X0 (M.op x sF0))
       have i₂ := eq399 X0 x sF0
       grind)
    | exact superpose eq399 eq1229
    | exact resolve eq1229 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1229 eq54
    | exact resolve eq54 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1229
  have eq1312 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) X1) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1295 eq544
    | exact resolve eq544 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq1313 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1295 eq551
    | exact resolve eq551 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq1326 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq1295 eq88
    | exact resolve eq88 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1295
  have eq1638 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op x (M.op y X1))) := by
    intro X0 X1
    first
    | exact superpose eq407 eq917
    | exact resolve eq917 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1639 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq408 eq917
    | exact resolve eq917 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1643 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq917 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq409 X0 X2 X3
       grind)
    | exact superpose eq409 eq917
    | exact resolve eq917 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1644 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X3 X2))) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq917 X1 (M.op (M.op X0 X2) (M.op X3 X2)) X3
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq917
    | exact resolve eq917 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1651 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq101 eq917
    | exact resolve eq917 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1653 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq513 eq917
    | exact resolve eq917 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq1658 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq93 eq917
    | exact resolve eq917 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1661 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq917 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq399 X0 X2 X2
       grind)
    | exact superpose eq399 eq917
    | exact resolve eq917 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1693 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op X2 X1)
       have i₂ := eq917 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq917 eq9
    | exact resolve eq9 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1748 : (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1658 eq117
    | exact resolve eq117 eq1658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1658
  have eq1770 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1653 eq549
    | exact resolve eq549 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq1653
  have eq1772 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1651 X0
       have i₂ := eq1661 sF4 sF2 sF3
       grind)
    | exact superpose eq1661 eq1651
    | exact resolve eq1651 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1796 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq832 X0 X1 X2 x
       have i₂ := eq1644 X2 X0 x X1
       grind)
    | exact superpose eq1644 eq832
    | exact resolve eq832 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq1800 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 (M.op X0 X4)) X2) = (M.op (M.op X1 (M.op X2 X4)) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq931 X2 X1 X0 x X4
       have i₂ := eq1644 X0 X1 x X4
       grind)
    | exact superpose eq1644 eq931
    | exact resolve eq931 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq1802 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1160 X0 X2 X1 x X4
       have i₂ := eq1644 X1 X4 x X2
       grind)
    | exact superpose eq1644 eq1160
    | exact resolve eq1160 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1803 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq834 X0 X1 X2 x
       have i₂ := eq1644 X2 X0 x (M.op X2 X1)
       grind)
    | exact superpose eq1644 eq834
    | exact resolve eq834 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq1809 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq810 X0 X1 X2 X3 X4 x
       have i₂ := eq1644 X4 (M.op X0 X4) x (M.op (M.op X2 X3) (M.op X1 X3))
       grind)
    | exact superpose eq1644 eq810
    | exact resolve eq810 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq1828 : ∀ X0 X2 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) (M.op X0 (M.op (σ y) X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq416 X0 X2 x
       have i₂ := eq1644 X0 sF4 X2 x
       grind)
    | exact superpose eq1644 eq416
    | exact resolve eq416 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq1644
  have eq1886 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq562 X0 X1 X2 X3 X4
       have i₂ := eq1643 X0 (M.op X3 (M.op X2 X4)) (M.op X1 X2) X1
       grind)
    | exact superpose eq1643 eq562
    | exact resolve eq562 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1908 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op X1 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq919 X0 X1 X2 X3 X4
       have i₂ := eq1643 X1 (M.op (M.op (M.op X0 X1) X2) X3) X4 X3
       grind)
    | exact superpose eq1643 eq919
    | exact resolve eq919 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq1910 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq393 x
       have i₂ := eq1643 y (M.op (M.op sF0 x) x) y x
       grind)
    | exact superpose eq1643 eq393
    | exact resolve eq393 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1914 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1313 X0
       have i₂ := eq1643 X0 (M.op sF0 X0) x sF0
       grind)
    | exact superpose eq1643 eq1313
    | exact resolve eq1313 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1917 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 x
       have i₂ := eq1643 X0 sF0 x y
       grind)
    | exact superpose eq1643 eq519
    | exact resolve eq519 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq1920 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 x
       have i₂ := eq1643 X0 sF4 x sF3
       grind)
    | exact superpose eq1643 eq520
    | exact resolve eq520 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq1979 : (k x (M.op (M.op x y) (M.op x y))) = (M.op x (M.op x (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1638 eq118
    | exact resolve eq118 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq2009 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) := by
    intro X0
    first
    | exact superpose eq1639 eq1772
    | exact resolve eq1772 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq2031 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op X2 (M.op X3 (M.op X1 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1809 X0 X1 X2 X3 X4
       have i₂ := eq1643 X2 X4 X3 (M.op X1 X3)
       grind)
    | exact superpose eq1643 eq1809
    | exact resolve eq1809 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq2052 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq1326
       have i₂ := eq1917 x sF0
       grind)
    | exact superpose eq1917 eq1326
    | exact resolve eq1326 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326 eq1917
  have eq2055 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1292 eq1914
    | exact resolve eq1914 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914
  have eq2057 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1910 x
       have i₂ := eq1803 (M.op (M.op sF0 x) x) x y
       grind)
    | exact superpose eq1803 eq1910
    | exact resolve eq1910 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910
  have eq2074 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1886 X0 X1 X2 X3 X4
       have i₂ := eq1802 (M.op X3 (M.op X2 X4)) (M.op X1 X2) X1 X0
       grind)
    | (have i₁ := eq1886 X0 X1 X2 X3 X4
       have i₂ := eq1802 (M.op X3 (M.op X2 X4)) X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq1802 eq1886
    | exact resolve eq1886 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq2137 : (k x (M.op (M.op x y) (M.op x y))) = (M.op x (M.op x x)) := by
    first
    | exact superpose eq535 eq1979
    | exact resolve eq1979 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq2168 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2009 X0
       have i₂ := eq534 X0 sF2 sF3
       grind)
    | exact superpose eq534 eq2009
    | exact resolve eq2009 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq2180 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2031 X0 X1 X2 x X4
       have i₂ := eq534 X2 x X1
       grind)
    | exact superpose eq534 eq2031
    | exact resolve eq2031 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2190 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq2052
       have i₂ := eq1802 sF0 sF0 y x
       grind)
    | (have i₁ := eq2052
       have i₂ := eq1802 sF0 y sF0 x
       grind)
    | exact superpose eq1802 eq2052
    | exact resolve eq2052 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2207 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2074 X0 x X2 X3 X4
       have i₂ := eq1803 X0 X2 x
       grind)
    | exact superpose eq1803 eq2074
    | exact resolve eq2074 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2074
  have eq2259 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq535 eq2190
    | exact resolve eq2190 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq2190
  have eq2342 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1770 eq53
    | exact resolve eq53 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2348 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) X1))) X2) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1770 eq53
    | exact resolve eq53 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2357 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2348 X0 x X1
       have i₂ := eq517 X0 X1 sF4 x
       grind)
    | exact superpose eq517 eq2348
    | exact resolve eq2348 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq2383 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op (M.op X0 (M.op X1 y)) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2055 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq399 X0 X1 y
       grind)
    | exact superpose eq399 eq2055
    | exact resolve eq2055 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2390 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X0) X1) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq2055 eq53
    | exact resolve eq53 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2396 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op x y) X1))) X2) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq2055 eq53
    | exact resolve eq53 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2405 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2396 X0 x X1
       have i₂ := eq517 X0 X1 sF0 x
       grind)
    | exact superpose eq517 eq2396
    | exact resolve eq2396 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq2415 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2383 x x
       have i₂ := eq1800 (M.op x (M.op x y)) sF0 x x
       grind)
    | (have i₁ := eq2383 X0 x
       have i₂ := eq1800 X0 sF0 (M.op X0 (M.op x y)) x
       grind)
    | exact superpose eq1800 eq2383
    | exact resolve eq2383 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2473 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq2168 eq399
    | exact resolve eq399 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2554 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2473 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq399 X0 X1 sF3
       grind)
    | exact superpose eq399 eq2473
    | exact resolve eq2473 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2656 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op (M.op (M.op X0 X2) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1803 X1 (M.op X2 X3) (M.op (M.op X0 X2) X3)
       have i₂ := eq409 X0 X2 X3
       grind)
    | exact superpose eq409 eq1803
    | exact resolve eq1803 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2677 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X0 X2) (M.op (M.op X3 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X2 (M.op X3 X1) X3
       have i₂ := eq1803 X0 X1 X3
       grind)
    | exact superpose eq1803 eq53
    | exact resolve eq53 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2694 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq407 (M.op y x)
       have i₂ := eq1803 (M.op sF0 (M.op y x)) x y
       grind)
    | exact superpose eq1803 eq407
    | exact resolve eq407 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2695 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq408 (M.op sF3 x)
       have i₂ := eq1803 (M.op sF4 (M.op sF3 x)) x sF3
       grind)
    | exact superpose eq1803 eq408
    | exact resolve eq408 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2728 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X0 X2) (M.op X3 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2677 X0 X1 X2 X3
       have i₂ := eq1643 X3 (M.op X0 X2) X1 X2
       grind)
    | exact superpose eq1643 eq2677
    | exact resolve eq2677 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677
  have eq2740 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op (M.op X0 X2) (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2656 X0 X1 X2 X3
       have i₂ := eq1643 (M.op X0 X2) X1 X3 X0
       grind)
    | exact superpose eq1643 eq2656
    | exact resolve eq2656 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2656
  have eq2766 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op X0 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2740 X0 X1 X2 X3
       have i₂ := eq1643 X0 X1 X2 (M.op X3 X0)
       grind)
    | exact superpose eq1643 eq2740
    | exact resolve eq2740 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740
  have eq2818 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2694 eq399
    | exact resolve eq399 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2915 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2695 eq399
    | exact resolve eq399 eq2695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695
  have eq2936 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2915 eq1920
    | exact resolve eq1920 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq3169 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op y y) X1)) = (M.op (M.op X0 (M.op (M.op x y) (M.op x x))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq2259 eq53
    | exact resolve eq53 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq3178 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op (M.op y y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3169 X0 X1
       have i₂ := eq517 X0 sF0 x x
       grind)
    | exact superpose eq517 eq3169
    | exact resolve eq3169 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq3169
  have eq3189 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op y (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3178 X0 X1
       have i₂ := eq1643 y (M.op X0 X1) y X1
       grind)
    | exact superpose eq1643 eq3178
    | exact resolve eq3178 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq3196 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3189 X0 X1
       have i₂ := eq1803 (M.op X0 X1) X1 y
       grind)
    | exact superpose eq1803 eq3189
    | exact resolve eq3189 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3189
  have eq3227 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq534 X1 (M.op X2 X3) (M.op (M.op X0 X2) X3)
       have i₂ := eq409 X0 X2 X3
       grind)
    | exact superpose eq409 eq534
    | exact resolve eq534 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3230 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq534 X3 X4 (M.op X0 (M.op X4 X2))
       have i₂ := eq53 X0 X1 X2 X4
       grind)
    | exact superpose eq53 eq534
    | exact resolve eq534 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3234 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) y)) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq614 eq534
    | exact resolve eq534 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3235 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (σ x)) (σ y))) = (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq656 eq534
    | exact resolve eq534 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3333 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (σ x)) (σ y))) = (M.op X1 (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq1639 eq3235
    | exact resolve eq3235 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3235
  have eq3334 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) y)) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | exact superpose eq1638 eq3234
    | exact resolve eq3234 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3234
  have eq3338 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3230 X0 X1 X2 X3 X4
       have i₂ := eq1643 X0 X4 X1 (M.op X2 X1)
       grind)
    | exact superpose eq1643 eq3230
    | exact resolve eq3230 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230
  have eq3341 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3227 X0 X1 X2 X3
       have i₂ := eq1643 X2 X1 X3 X0
       grind)
    | exact superpose eq1643 eq3227
    | exact resolve eq3227 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq3363 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3333 X0 X1
       have i₂ := eq1643 X0 X1 sF2 sF3
       grind)
    | exact superpose eq1643 eq3333
    | exact resolve eq3333 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3333
  have eq3364 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3334 X0 X1
       have i₂ := eq1643 X0 X1 x y
       grind)
    | exact superpose eq1643 eq3334
    | exact resolve eq3334 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334
  have eq3367 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3338 X0 x X2 X3 X4
       have i₂ := eq534 X0 x X2
       grind)
    | exact superpose eq534 eq3338
    | exact resolve eq3338 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3370 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 X3))) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3341 X0 X1 X2 X3
       have i₂ := eq1643 X0 X1 X2 X3
       grind)
    | exact superpose eq1643 eq3341
    | exact resolve eq3341 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341
  have eq3385 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq3363
    | (have j0 := eq3363 X0 X1
       grind)
    | exact resolve eq3363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq3386 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3364 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3364
    | (have j0 := eq3364 X0 X1
       grind)
    | exact resolve eq3364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq3467 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1803 X1 (M.op X2 X2) X0
       have i₂ := eq1661 X0 X0 X2
       grind)
    | exact superpose eq1661 eq1803
    | exact resolve eq1803 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3469 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq399 X0 X1 (M.op X2 X2)
       have i₂ := eq1661 X1 X0 X2
       grind)
    | exact superpose eq1661 eq399
    | exact resolve eq399 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3470 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X2 (M.op X3 X3) X1
       have i₂ := eq1661 X1 X0 X3
       grind)
    | exact superpose eq1661 eq53
    | exact resolve eq53 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3488 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq409 X0 X1 (M.op X2 X2)
       have i₂ := eq1661 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X2
       grind)
    | exact superpose eq1661 eq409
    | exact resolve eq409 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3500 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2694 (M.op x x)
       have i₂ := eq1661 y sF0 x
       grind)
    | exact superpose eq1661 eq2694
    | exact resolve eq2694 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq3535 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3470 X0 X1 X2 X3
       have i₂ := eq1643 X3 (M.op X0 X2) X3 X2
       grind)
    | exact superpose eq1643 eq3470
    | exact resolve eq3470 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3470
  have eq3567 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3535 X0 X1 X2 x
       have i₂ := eq1803 (M.op X0 X2) X2 x
       grind)
    | exact superpose eq1803 eq3535
    | exact resolve eq3535 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535
  have eq3694 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) (M.op x y)) = (M.op (M.op X1 X0) (M.op (M.op X0 X2) (M.op x X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 X1 (M.op (M.op X0 X2) (M.op x X2))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq90
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq3776 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) (M.op x y)) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op x X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3694 X0 X1 X2
       have i₂ := eq1643 X0 (M.op X1 X0) X2 (M.op x X2)
       grind)
    | exact superpose eq1643 eq3694
    | exact resolve eq3694 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3694
  have eq3808 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op x y)) = (M.op (M.op X1 X0) (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq3776 X0 X1 x
       have i₂ := eq534 X0 x x
       grind)
    | exact superpose eq534 eq3776
    | exact resolve eq3776 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3776
  have eq3919 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op (M.op x y) y) X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq3500 eq53
    | exact resolve eq53 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3500
  have eq4316 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 X1) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq614 eq1693
    | exact resolve eq1693 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4319 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 X1) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq656 eq1693
    | exact resolve eq1693 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq4386 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq399 (M.op (M.op X0 X2) X1) X1 X2
       have i₂ := eq1693 X0 X2 X1
       grind)
    | exact superpose eq1693 eq399
    | exact resolve eq399 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq4452 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1312 X0 X1
       have i₂ := eq4386 X0 (M.op X1 y) X1
       grind)
    | (have i₁ := eq1312 X0 X1
       have i₂ := eq4386 X0 X1 (M.op X1 y)
       grind)
    | exact superpose eq4386 eq1312
    | exact resolve eq1312 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq4455 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2554 X0 x
       have i₂ := eq4386 X0 (M.op x sF3) x
       grind)
    | (have i₁ := eq2554 X0 X1
       have i₂ := eq4386 X0 X1 (M.op X1 sF3)
       grind)
    | exact superpose eq4386 eq2554
    | exact resolve eq2554 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq4468 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1146 X0 X1 X2 X3 X4
       have i₂ := eq4386 (M.op (M.op X0 X1) X2) (M.op X4 X3) X4
       grind)
    | (have i₁ := eq1146 X0 X1 X2 X3 X4
       have i₂ := eq4386 (M.op (M.op X0 X1) X2) X4 (M.op X4 X3)
       grind)
    | exact superpose eq4386 eq1146
    | exact resolve eq1146 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq4484 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 x) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2405 X0 X1
       have i₂ := eq4386 X0 (M.op X1 y) x
       grind)
    | (have i₁ := eq2405 X0 X1
       have i₂ := eq4386 X0 x (M.op X1 y)
       grind)
    | exact superpose eq4386 eq2405
    | exact resolve eq2405 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq4505 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2357 X0 X1
       have i₂ := eq4386 X0 (M.op X1 sF3) sF2
       grind)
    | (have i₁ := eq2357 X0 X1
       have i₂ := eq4386 X0 sF2 (M.op X1 sF3)
       grind)
    | exact superpose eq4386 eq2357
    | exact resolve eq2357 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq4762 : (k (τ (σ x)) (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq1748 eq204
    | exact resolve eq204 eq1748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq1748
  have eq4763 : (τ (M.op (σ x) (M.op (σ x) (σ x)))) = (k (τ (σ x)) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq4762
       have i₂ := eq236 sF4
       grind)
    | exact superpose eq236 eq4762
    | exact resolve eq4762 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4762
  have eq4767 : (τ (M.op (σ x) (M.op (σ x) (σ x)))) = (k x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq38 eq4763
    | exact resolve eq4763 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4763
  have eq5360 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) X0) X0) x) := by
    intro X0
    first
    | (have i₁ := eq2057 x
       have i₂ := eq3196 sF0 x
       grind)
    | (have i₁ := eq2057 x
       have i₂ := eq3196 sF0 x
       grind)
    | exact superpose eq3196 eq2057
    | exact resolve eq2057 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq6560 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X1)) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3469 (M.op (M.op X0 X1) X2) (M.op X2 X1) X3
       have i₂ := eq1693 X0 X1 X2
       grind)
    | exact superpose eq1693 eq3469
    | exact resolve eq3469 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6565 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 (M.op x y)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq614 eq3469
    | exact resolve eq3469 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7377 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq1770 eq3567
    | exact resolve eq3567 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7378 : ∀ X0 X1 : G, (M.op x (M.op X0 y)) = (M.op (M.op (M.op (M.op x y) X0) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq2055 eq3567
    | exact resolve eq3567 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7383 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) x) X1) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3567 (M.op X0 X1) X2 X1
       have i₂ := eq3196 X0 X1
       grind)
    | (have i₁ := eq3567 (M.op X0 x) X1 x
       have i₂ := eq3196 X0 X1
       grind)
    | exact superpose eq3196 eq3567
    | exact resolve eq3567 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7790 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op (M.op x y) X0) X1) (M.op y X0)) := by
    intro X0 X1
    first
    | exact superpose eq407 eq4386
    | exact resolve eq4386 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq7791 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq408 eq4386
    | exact resolve eq4386 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq7792 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1770 eq4386
    | exact resolve eq4386 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7793 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op (M.op x y) X0) X1) (M.op X0 y)) := by
    intro X0 X1
    first
    | exact superpose eq2055 eq4386
    | exact resolve eq4386 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7796 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) x) X2) = (M.op (M.op (M.op X0 X1) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4386 (M.op X0 X1) X2 X1
       have i₂ := eq3196 X0 X1
       grind)
    | (have i₁ := eq4386 (M.op X0 x) X1 x
       have i₂ := eq3196 X0 X1
       grind)
    | exact superpose eq3196 eq4386
    | exact resolve eq4386 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7799 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 X2) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4386 (M.op X0 X2) X3 X1
       have i₂ := eq4386 X0 X2 X1
       grind)
    | (have i₁ := eq4386 (M.op X0 X2) X3 X1
       have i₂ := eq4386 X0 X1 X2
       grind)
    | exact superpose eq4386 eq4386
    | exact resolve eq4386 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7807 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 x) y) X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq614 eq4386
    | exact resolve eq4386 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq7875 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X2)) = (M.op X3 (M.op X1 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq534 X3 X1 (M.op X0 X2)
       have i₂ := eq4386 X0 X2 X1
       grind)
    | (have i₁ := eq534 X3 X1 (M.op X0 X2)
       have i₂ := eq4386 X0 X1 X2
       grind)
    | exact superpose eq4386 eq534
    | exact resolve eq534 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7891 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op X0 X3) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1796 (M.op X0 X3) X1 X2
       have i₂ := eq4386 X0 X3 (M.op X1 X2)
       grind)
    | (have i₁ := eq1796 (M.op X0 X3) X1 X2
       have i₂ := eq4386 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq4386 eq1796
    | exact resolve eq1796 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7926 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X2)) = (M.op X3 (M.op X1 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7875 X0 X1 X2 X3
       have i₂ := eq1643 X0 X1 X1 X2
       grind)
    | exact superpose eq1643 eq7875
    | exact resolve eq7875 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7875
  have eq8052 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) X0) x) X0) := by
    intro X0
    first
    | exact superpose eq5360 eq4386
    | exact resolve eq4386 eq5360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5360
  have eq9978 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) = (M.op X0 (M.op (M.op X1 (M.op (σ y) X2)) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1828 eq534
    | exact resolve eq534 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq10003 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) = (M.op X0 (M.op X1 (M.op (M.op (σ y) X2) (σ x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9978 X1 X0 X2
       have i₂ := eq1643 X0 X1 (M.op sF3 X2) sF2
       grind)
    | exact superpose eq1643 eq9978
    | exact resolve eq9978 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9978
  have eq10119 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) = (M.op X0 (M.op X1 (M.op (σ x) (M.op (σ y) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10003 X0 x X2
       have i₂ := eq1802 X0 (M.op sF3 X2) sF2 x
       grind)
    | (have i₁ := eq10003 X0 x X2
       have i₂ := eq1802 X0 sF2 (M.op sF3 X2) x
       grind)
    | exact superpose eq1802 eq10003
    | exact resolve eq10003 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10003
  have eq10205 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (σ x) (M.op (σ y) X2)))) = (M.op X0 (M.op (σ x) (M.op (σ y) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1639 eq10119
    | exact resolve eq10119 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10119
  have eq11493 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op x y) X1) X0)) = (M.op X2 (M.op X0 (M.op x (M.op y X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1638 eq1796
    | exact resolve eq1796 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11607 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op x y) (M.op X1 X0))) = (M.op X2 (M.op X0 (M.op x (M.op y X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11493 x X2 X1
       have i₂ := eq1643 sF0 X1 X2 x
       grind)
    | exact superpose eq1643 eq11493
    | exact resolve eq11493 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11493
  have eq11700 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x (M.op y (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op x (M.op y X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1638 eq11607
    | exact resolve eq11607 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11607
  have eq12549 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 x)) (M.op X2 X2)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3808 eq3488
    | exact resolve eq3488 eq3808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq12607 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) (M.op X1 x)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12549 X0 X1 X2
       have i₂ := eq7799 (M.op X0 X1) (M.op X1 x) (M.op X2 X2) sF0
       grind)
    | (have i₁ := eq12549 X0 X1 X2
       have i₂ := eq7799 (M.op X0 X1) sF0 (M.op X1 x) (M.op X2 X2)
       grind)
    | exact superpose eq7799 eq12549
    | exact resolve eq12549 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12549
  have eq12709 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12607 X0 x x
       have i₂ := eq6560 (M.op (M.op X0 x) sF0) x x x
       grind)
    | exact superpose eq6560 eq12607
    | exact resolve eq12607 eq6560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12607
  have eq12790 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op X0 X1) x) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq12709 X0 x
       have i₂ := eq7799 (M.op X0 x) sF0 x x
       grind)
    | (have i₁ := eq12709 X0 X1
       have i₂ := eq7799 (M.op X0 X1) X1 sF0 x
       grind)
    | exact superpose eq7799 eq12709
    | exact resolve eq12709 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12709
  have eq12953 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 y)) = (M.op (M.op (M.op X0 x) X1) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4452 (M.op X0 X1) X2
       have i₂ := eq4386 X0 X1 x
       grind)
    | (have i₁ := eq4452 (M.op X0 X1) X2
       have i₂ := eq4386 X0 x X1
       grind)
    | exact superpose eq4386 eq4452
    | exact resolve eq4452 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13000 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4452 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       have i₂ := eq3488 X0 X1 X2
       grind)
    | exact superpose eq3488 eq4452
    | exact resolve eq4452 eq3488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13062 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 y)) (M.op X2 X2)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq4452 eq3488
    | exact resolve eq3488 eq4452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4452
  have eq13167 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) (M.op X1 y)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13062 X0 X1 X2
       have i₂ := eq7799 (M.op X0 X1) (M.op X1 y) (M.op X2 X2) sF0
       grind)
    | (have i₁ := eq13062 X0 X1 X2
       have i₂ := eq7799 (M.op X0 X1) sF0 (M.op X1 y) (M.op X2 X2)
       grind)
    | exact superpose eq7799 eq13062
    | exact resolve eq13062 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13062
  have eq13217 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13000 X0 X1 X2
       have i₂ := eq7799 (M.op X0 X1) (M.op X2 X2) x sF0
       grind)
    | (have i₁ := eq13000 X0 X1 X2
       have i₂ := eq7799 (M.op X0 X1) sF0 (M.op X2 X2) x
       grind)
    | exact superpose eq7799 eq13000
    | exact resolve eq13000 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13000
  have eq13293 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X1) (M.op x y)) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13167 X0 x x
       have i₂ := eq6560 (M.op (M.op X0 x) sF0) y x x
       grind)
    | exact superpose eq6560 eq13167
    | exact resolve eq13167 eq6560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13167
  have eq13330 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 X1) x) x) y) := by
    intro X0 X1
    first
    | exact superpose eq6565 eq13217
    | exact resolve eq13217 eq6565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6565 eq13217
  have eq13390 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X1) y) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13293 X0 x
       have i₂ := eq7799 (M.op X0 x) sF0 y x
       grind)
    | (have i₁ := eq13293 X0 X1
       have i₂ := eq7799 (M.op X0 X1) X1 sF0 y
       grind)
    | exact superpose eq7799 eq13293
    | exact resolve eq13293 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13293
  have eq14919 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op x y) X0) X2)) = (M.op X1 (M.op (M.op y X2) (M.op x X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2390 eq534
    | exact resolve eq534 eq2390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq14950 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op x y) X0) X2)) = (M.op X1 (M.op y (M.op X2 (M.op x X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14919 X0 X1 X2
       have i₂ := eq1643 y X1 X2 (M.op x X0)
       grind)
    | exact superpose eq1643 eq14919
    | exact resolve eq14919 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14919
  have eq15036 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y (M.op X2 (M.op x X0)))) = (M.op X1 (M.op (M.op x y) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14950 X2 X1 x
       have i₂ := eq1643 sF0 X1 X2 x
       grind)
    | exact superpose eq1643 eq14950
    | exact resolve eq14950 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14950
  have eq15084 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y (M.op X2 (M.op x X0)))) = (M.op X1 (M.op x (M.op y (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1638 eq15036
    | exact resolve eq15036 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15036
  have eq16146 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op y (M.op X0 (M.op x X0))))) := by
    intro X0
    first
    | (have i₁ := eq135 (M.op x X0)
       have i₂ := eq2818 X0 (M.op x X0)
       grind)
    | exact superpose eq2818 eq135
    | exact resolve eq135 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16168 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) (M.op y (M.op X0 X1))) (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3488 (M.op x X0) X1 X2
       have i₂ := eq2818 X0 X1
       grind)
    | exact superpose eq2818 eq3488
    | exact resolve eq3488 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16181 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) (M.op X2 X1)) = (M.op (M.op x y) (M.op y (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1796 (M.op x X0) X1 X2
       have i₂ := eq2818 X0 (M.op X1 X2)
       grind)
    | exact superpose eq2818 eq1796
    | exact resolve eq1796 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16226 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op y (M.op X0 (M.op X2 X1)))) = (M.op (M.op x y) (M.op y (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16181 X0 X1 X2
       have i₂ := eq2818 X0 (M.op X2 X1)
       grind)
    | exact superpose eq2818 eq16181
    | exact resolve eq16181 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16181
  have eq16239 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) (M.op y (M.op X0 X1))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16168 X0 x X2
       have i₂ := eq7799 sF0 (M.op y (M.op X0 x)) (M.op X2 X2) x
       grind)
    | (have i₁ := eq16168 X0 X1 X2
       have i₂ := eq7799 sF0 X1 (M.op y (M.op X0 X1)) (M.op X2 X2)
       grind)
    | exact superpose eq7799 eq16168
    | exact resolve eq16168 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16168
  have eq16259 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x (M.op y (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq16146 X0
       have i₂ := eq15084 X0 sF0 X0
       grind)
    | exact superpose eq15084 eq16146
    | exact resolve eq16146 eq15084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15084 eq16146
  have eq16337 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) (M.op X0 X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16239 X0 X1 x
       have i₂ := eq6560 (M.op sF0 X1) (M.op X0 X1) y x
       grind)
    | exact superpose eq6560 eq16239
    | exact resolve eq16239 eq6560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16239
  have eq16357 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16259 X0
       have i₂ := eq1661 y x X0
       grind)
    | exact superpose eq1661 eq16259
    | exact resolve eq16259 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16259
  have eq16414 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16337 X1 x
       have i₂ := eq7891 (M.op sF0 x) X1 x y
       grind)
    | exact superpose eq7891 eq16337
    | exact resolve eq16337 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16337
  have eq16427 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq16357 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16357
    | (have j0 := eq16357 X0
       grind)
    | exact resolve eq16357 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357
  have eq16476 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq16427 X0
       have i₂ := eq135 sF0
       grind)
    | exact superpose eq135 eq16427
    | exact resolve eq16427 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16427
  have eq16501 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq16476
    | (have j0 := eq16476 X0
       grind)
    | exact resolve eq16476 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16476
  have eq16874 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) (M.op X2 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2915 eq1796
    | exact resolve eq1796 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16921 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X2 X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2915 eq16874
    | exact resolve eq16874 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16874
  have eq17370 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4484 (M.op X0 sF0) X1
       have i₂ := eq3567 X0 sF0 X2
       grind)
    | (have i₁ := eq4484 (M.op X0 sF0) X1
       have i₂ := eq3567 X0 X1 sF0
       grind)
    | exact superpose eq3567 eq4484
    | exact resolve eq4484 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17457 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op X0 y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq4484 eq2342
    | exact resolve eq2342 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17459 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 x) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq4484 eq4386
    | exact resolve eq4386 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17551 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 x) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1796 (M.op X0 x) X1 y
       have i₂ := eq4484 X0 X1
       grind)
    | exact superpose eq4484 eq1796
    | exact resolve eq1796 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17556 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 x)) = (M.op X2 (M.op (M.op X1 y) (M.op (M.op X0 (M.op x y)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq534 X2 (M.op X1 y) (M.op X0 x)
       have i₂ := eq4484 X0 X1
       grind)
    | exact superpose eq4484 eq534
    | exact resolve eq534 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484
  have eq17588 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 x)) = (M.op X2 (M.op X1 (M.op y (M.op (M.op X0 (M.op x y)) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17556 X0 X0 X1
       have i₂ := eq1643 X0 X1 y (M.op (M.op X0 sF0) X0)
       grind)
    | exact superpose eq1643 eq17556
    | exact resolve eq17556 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17556
  have eq17765 : (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)) y) := by
    first
    | (have i₁ := eq17457 x
       have i₂ := eq2207 (M.op x y) x (M.op sF4 x) (M.op sF3 x)
       grind)
    | (have i₁ := eq17457 x
       have i₂ := eq2207 sF3 x (M.op sF4 x) y
       grind)
    | exact superpose eq2207 eq17457
    | exact resolve eq17457 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17457
  have eq17844 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17370 X0 X1 X2
       have i₂ := eq4386 X0 sF0 x
       grind)
    | (have i₁ := eq17370 X0 X1 X2
       have i₂ := eq4386 X0 x sF0
       grind)
    | exact superpose eq4386 eq17370
    | exact resolve eq17370 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17370
  have eq17861 : ∀ X0 X2 : G, (M.op X2 (M.op X0 x)) = (M.op X2 (M.op y (M.op X0 (M.op x y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq17588 X0 X0 x
       have i₂ := eq2766 X0 x y (M.op X0 sF0)
       grind)
    | exact superpose eq2766 eq17588
    | (have j1 := eq2766 y X2 X0 x
       grind)
    | exact resolve eq17588 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766 eq17588
  have eq17994 : (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) y) (σ y)) := by
    first
    | (have i₁ := eq17765
       have i₂ := eq4386 (M.op sF4 x) sF3 y
       grind)
    | (have i₁ := eq17765
       have i₂ := eq4386 (M.op sF4 x) y sF3
       grind)
    | exact superpose eq4386 eq17765
    | exact resolve eq17765 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17765
  have eq18057 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) x) (M.op y (M.op X2 y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq17551 eq17844
    | exact resolve eq17844 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17844
  have eq18194 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18057 X0 X1 X2
       have i₂ := eq534 (M.op (M.op X0 x) x) y X2
       grind)
    | exact superpose eq534 eq18057
    | exact resolve eq18057 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18057
  have eq18350 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) x) y)) (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq17994 eq1770
    | exact resolve eq1770 eq17994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770 eq17994
  have eq18391 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op x y)) y)) (M.op (M.op (σ x) (σ y)) x)) := by
    first
    | (have i₁ := eq18350
       have i₂ := eq1800 (M.op sF4 x) sF4 (M.op sF2 sF0) y
       grind)
    | (have i₁ := eq18350
       have i₂ := eq1800 (M.op sF2 sF0) sF4 (M.op sF4 x) y
       grind)
    | exact superpose eq1800 eq18350
    | exact resolve eq18350 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18350
  have eq18414 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) x)) (M.op y (M.op (σ x) (M.op x y)))) := by
    first
    | (have i₁ := eq18391
       have i₂ := eq7891 sF4 (M.op sF2 sF0) y (M.op sF4 x)
       grind)
    | (have i₁ := eq18391
       have i₂ := eq7891 sF4 x sF4 (M.op (M.op sF2 sF0) y)
       grind)
    | exact superpose eq7891 eq18391
    | exact resolve eq18391 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18391
  have eq18437 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op y (M.op (σ x) (M.op x y)))) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq18414
       have i₂ := eq7891 sF4 sF4 x (M.op y (M.op sF2 sF0))
       grind)
    | (have i₁ := eq18414
       have i₂ := eq7891 sF4 (M.op sF2 sF0) y (M.op sF4 x)
       grind)
    | exact superpose eq7891 eq18414
    | exact resolve eq18414 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18414
  have eq18458 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (M.op x y)) y)) := by
    first
    | (have i₁ := eq18437
       have i₂ := eq7891 sF4 y (M.op sF2 sF0) (M.op x sF4)
       grind)
    | (have i₁ := eq18437
       have i₂ := eq7891 sF4 sF4 x (M.op y (M.op sF2 sF0))
       grind)
    | exact superpose eq7891 eq18437
    | exact resolve eq18437 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18437
  have eq18474 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq18458
       have i₂ := eq1643 sF2 (M.op sF4 (M.op x sF4)) sF0 y
       grind)
    | exact superpose eq1643 eq18458
    | exact resolve eq18458 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18458
  have eq18488 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op (σ x) (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq18474
       have i₂ := eq1802 (M.op sF4 (M.op x sF4)) sF0 y sF2
       grind)
    | (have i₁ := eq18474
       have i₂ := eq1802 (M.op sF4 (M.op x sF4)) y sF0 sF2
       grind)
    | exact superpose eq1802 eq18474
    | exact resolve eq18474 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18474
  have eq18499 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op y (M.op (σ x) (M.op x y)))) := by
    first
    | (have i₁ := eq18488
       have i₂ := eq3367 sF2 sF0 (M.op sF4 (M.op x sF4)) y
       grind)
    | (have i₁ := eq18488
       have i₂ := eq3367 y sF0 (M.op sF4 (M.op x sF4)) sF2
       grind)
    | exact superpose eq3367 eq18488
    | exact resolve eq18488 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18488
  have eq18508 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op (σ x) x)) := by
    first
    | exact superpose eq17861 eq18499
    | exact resolve eq18499 eq17861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17861 eq18499
  have eq18515 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18508
       have i₂ := eq2207 (M.op x sF4) x sF4 (M.op sF2 x)
       grind)
    | (have i₁ := eq18508
       have i₂ := eq2207 sF2 x sF4 sF4
       grind)
    | exact superpose eq2207 eq18508
    | exact resolve eq18508 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18508
  have eq18875 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) = (M.op X2 (M.op (M.op X0 (σ x)) (M.op X1 (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4505 eq1796
    | exact resolve eq1796 eq4505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18920 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq4505 eq1796
    | exact resolve eq1796 eq4505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4505
  have eq19010 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) = (M.op X2 (M.op X0 (M.op (σ x) (M.op X1 (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18875 X0 X1 X1
       have i₂ := eq1643 X0 X1 sF2 (M.op X1 sF3)
       grind)
    | exact superpose eq1643 eq18875
    | exact resolve eq18875 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18875
  have eq21116 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ x) (M.op X0 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3385 x X1
       have i₂ := eq1796 sF2 sF3 x
       grind)
    | (have i₁ := eq3385 X1 X1
       have i₂ := eq1796 sF2 X1 sF3
       grind)
    | exact superpose eq1796 eq3385
    | exact resolve eq3385 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21299 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) = (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq3385 eq2915
    | exact resolve eq2915 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21322 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) X1))) := by
    intro X0 X1
    first
    | exact superpose eq2915 eq21299
    | exact resolve eq21299 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21299
  have eq21506 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21322 X0 x
       have i₂ := eq1643 X0 sF3 sF4 x
       grind)
    | exact superpose eq1643 eq21322
    | exact resolve eq21322 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21322
  have eq21628 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (M.op (M.op (σ y) X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq21506 X0 x
       have i₂ := eq1643 sF2 sF3 (M.op sF3 X0) x
       grind)
    | exact superpose eq1643 eq21506
    | exact resolve eq21506 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21506
  have eq21717 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq21628 X0 X1
       have i₂ := eq3367 sF3 (M.op (M.op sF3 X0) X1) sF4 sF2
       grind)
    | (have i₁ := eq21628 X0 X1
       have i₂ := eq3367 sF2 (M.op (M.op sF3 X0) X1) sF4 sF3
       grind)
    | exact superpose eq3367 eq21628
    | exact resolve eq21628 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21628
  have eq21763 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq21717 x x
       have i₂ := eq1643 sF3 sF3 x x
       grind)
    | exact superpose eq1643 eq21717
    | exact resolve eq21717 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21717
  have eq21783 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21763 X0 X1
       have i₂ := eq1803 sF2 (M.op X0 X1) sF3
       grind)
    | exact superpose eq1803 eq21763
    | exact resolve eq21763 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21763
  have eq21793 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (σ y) X1))))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq1639 eq21783
    | exact resolve eq21783 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21783
  have eq21993 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op x y)))) = (M.op X2 (M.op (M.op x (M.op y X1)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1796 X2 X0 (M.op x (M.op y X1))
       have i₂ := eq3386 X1 X0
       grind)
    | exact superpose eq3386 eq1796
    | exact resolve eq1796 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386
  have eq22112 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op x y)))) = (M.op X2 (M.op x (M.op (M.op y X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21993 X0 X1 X2
       have i₂ := eq1643 x X2 (M.op y X1) X0
       grind)
    | exact superpose eq1643 eq21993
    | exact resolve eq21993 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21993
  have eq22296 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x (M.op y (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22112 X0 X1 X2
       have i₂ := eq1643 y x X1 X0
       grind)
    | exact superpose eq1643 eq22112
    | exact resolve eq22112 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22112
  have eq22702 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) X0) x)) = (M.op (M.op (M.op (M.op x y) y) X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq8052 eq3919
    | exact resolve eq3919 eq8052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3919 eq8052
  have eq22866 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) X0) x)) = (M.op (M.op (M.op (M.op x y) y) X0) y) := by
    intro X0
    first
    | exact superpose eq1292 eq22702
    | exact resolve eq22702 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22702
  have eq22976 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) x) X0) = (M.op x (M.op (M.op (M.op x y) X0) x)) := by
    intro X0
    first
    | (have i₁ := eq22866 x
       have i₂ := eq7796 sF0 y x
       grind)
    | exact superpose eq7796 eq22866
    | exact resolve eq22866 eq7796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7796 eq22866
  have eq23052 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) x) X0) = (M.op x (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq22976 x
       have i₂ := eq1643 sF0 x x x
       grind)
    | exact superpose eq1643 eq22976
    | exact resolve eq22976 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22976
  have eq23097 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) x) X0) = (M.op x (M.op x (M.op y (M.op X0 x)))) := by
    intro X0
    first
    | exact superpose eq1638 eq23052
    | exact resolve eq23052 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23052
  have eq23123 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) x) X0) = (M.op x (M.op x (M.op x (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq23097 X0
       have i₂ := eq11700 x X0 x
       grind)
    | exact superpose eq11700 eq23097
    | exact resolve eq23097 eq11700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11700 eq23097
  have eq23137 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op (M.op (M.op x y) x) x) X0) := by
    intro X0
    first
    | (have i₁ := eq23123 X0
       have i₂ := eq1803 x (M.op y X0) x
       grind)
    | exact superpose eq1803 eq23123
    | exact resolve eq23123 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23123
  have eq23221 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) x) y) = (M.op X0 (M.op (M.op X2 X1) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4316 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq1693 X0 X1 X2
       grind)
    | exact superpose eq1693 eq4316
    | exact resolve eq4316 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23491 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op x y)))) = (M.op (M.op (M.op (M.op X0 X1) X2) x) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23221 X1 X2 X0
       have i₂ := eq1643 X0 X1 X2 sF0
       grind)
    | exact superpose eq1643 eq23221
    | exact resolve eq23221 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23221
  have eq23641 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13330 X0 X1
       have i₂ := eq23491 X0 X1 x
       grind)
    | exact superpose eq23491 eq13330
    | exact resolve eq13330 eq23491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13330
  have eq24005 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) X0) (M.op (M.op (σ y) X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2342 eq4319
    | exact resolve eq4319 eq2342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq24015 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (σ x)) (σ y)) = (M.op X0 (M.op (M.op X2 X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4319 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq1693 X0 X1 X2
       grind)
    | exact superpose eq1693 eq4319
    | exact resolve eq4319 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319
  have eq24257 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op (σ x) (σ y))))) = (M.op (M.op (M.op (M.op X0 X1) X2) (σ x)) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24015 X1 X2 X0
       have i₂ := eq1643 X0 X1 X2 sF4
       grind)
    | exact superpose eq1643 eq24015
    | exact resolve eq24015 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24015
  have eq24265 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ y) X1) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq2915 eq24005
    | exact resolve eq24005 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24005
  have eq24402 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1))))) := by
    intro X0 X1
    first
    | exact superpose eq16921 eq24265
    | exact resolve eq24265 eq16921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16921 eq24265
  have eq24492 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ y) X1)))))) := by
    intro X0 X1
    first
    | exact superpose eq1639 eq24402
    | exact resolve eq24402 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24402
  have eq24556 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq21793 eq24492
    | exact resolve eq24492 eq21793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21793 eq24492
  have eq24593 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq24257 eq24556
    | exact resolve eq24556 eq24257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24257 eq24556
  have eq25151 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op X0 X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op x (M.op (M.op X0 (M.op X1 y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2415 eq4455
    | exact resolve eq4455 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415 eq4455
  have eq25407 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op X0 X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op x (M.op X0 (M.op (M.op X1 y) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25151 X0 X1
       have i₂ := eq1643 X0 x (M.op X1 y) sF3
       grind)
    | exact superpose eq1643 eq25151
    | exact resolve eq25151 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25151
  have eq25553 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op X0 X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op x (M.op X0 (M.op (σ y) (M.op X1 y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25407 x X1
       have i₂ := eq1802 x (M.op X1 y) sF3 x
       grind)
    | (have i₁ := eq25407 x X1
       have i₂ := eq1802 x sF3 (M.op X1 y) x
       grind)
    | exact superpose eq1802 eq25407
    | exact resolve eq25407 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25407
  have eq25668 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (M.op X0 X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op x (M.op X0 (M.op y (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25553 X1 x
       have i₂ := eq3370 sF3 X1 x y
       grind)
    | (have i₁ := eq25553 X1 x
       have i₂ := eq3370 y X1 sF3 x
       grind)
    | exact superpose eq3370 eq25553
    | exact resolve eq25553 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25553
  have eq25746 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (σ x)) (M.op (σ x) (σ y))) (M.op X0 X1)) = (M.op x (M.op X0 (M.op y (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25668 X0 X1
       have i₂ := eq7799 sF0 (M.op X0 X1) sF2 sF4
       grind)
    | (have i₁ := eq25668 X0 X1
       have i₂ := eq7799 sF0 sF4 (M.op X0 X1) sF2
       grind)
    | exact superpose eq7799 eq25668
    | exact resolve eq25668 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25668
  have eq25791 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) (σ x)) (σ x)) (M.op (σ y) (M.op X0 X1))) = (M.op x (M.op X0 (M.op y (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq18920 eq25746
    | exact resolve eq25746 eq18920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18920 eq25746
  have eq25819 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) x) x) (M.op (σ y) (M.op X0 X1))) = (M.op x (M.op X0 (M.op y (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25791 X0 X1
       have i₂ := eq18194 sF0 sF2 (M.op sF3 (M.op X0 X1))
       grind)
    | exact superpose eq18194 eq25791
    | exact resolve eq25791 eq18194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18194 eq25791
  have eq25837 : ∀ X0 X1 : G, (M.op x (M.op y (M.op (σ y) (M.op X0 X1)))) = (M.op x (M.op X0 (M.op y (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq23137 eq25819
    | exact resolve eq25819 eq23137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23137 eq25819
  have eq26423 : ∀ X0 X1 : G, (M.op x (M.op X1 y)) = (M.op (M.op (M.op (M.op x y) X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7378 X1 x
       have i₂ := eq4386 sF0 X1 x
       grind)
    | (have i₁ := eq7378 x X1
       have i₂ := eq4386 sF0 X1 x
       grind)
    | exact superpose eq4386 eq7378
    | exact resolve eq7378 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7378
  have eq27054 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op y X2) (M.op x X0))) = (M.op X1 (M.op (M.op (M.op x y) X2) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7790 eq534
    | exact resolve eq534 eq7790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7790
  have eq27095 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op y X2) (M.op x X0))) = (M.op X1 (M.op (M.op x y) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27054 x X1 X2
       have i₂ := eq1643 sF0 X1 X2 x
       grind)
    | exact superpose eq1643 eq27054
    | exact resolve eq27054 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27054
  have eq27191 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op y X2) (M.op x X0))) = (M.op X1 (M.op x (M.op y (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1638 eq27095
    | exact resolve eq27095 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27095
  have eq27242 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y (M.op X2 (M.op x X0)))) = (M.op X1 (M.op x (M.op y (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27191 X0 X1 X2
       have i₂ := eq1643 y X1 X2 (M.op x X0)
       grind)
    | exact superpose eq1643 eq27191
    | exact resolve eq27191 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27191
  have eq27440 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ y) X2) (M.op (σ x) X0))) = (M.op X1 (M.op (M.op (M.op (σ x) (σ y)) X2) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7791 eq534
    | exact resolve eq534 eq7791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7791
  have eq27481 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ y) X2) (M.op (σ x) X0))) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27440 x X1 X2
       have i₂ := eq1643 sF4 X1 X2 x
       grind)
    | exact superpose eq1643 eq27440
    | exact resolve eq27440 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27440
  have eq27588 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ y) X2) (M.op (σ x) X0))) = (M.op X1 (M.op (σ x) (M.op (σ y) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1639 eq27481
    | exact resolve eq27481 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27481
  have eq27650 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) (M.op X2 (M.op (σ x) X0)))) = (M.op X1 (M.op (σ x) (M.op (σ y) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27588 X0 X1 X2
       have i₂ := eq1643 sF3 X1 X2 (M.op sF2 X0)
       grind)
    | exact superpose eq1643 eq27588
    | exact resolve eq27588 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27588
  have eq28210 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x y) X1) X0) x) y) = (M.op (M.op x X0) (M.op (M.op X1 y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq7793 eq4316
    | exact resolve eq4316 eq7793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7793
  have eq28221 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x y) X1) X0) x) y) = (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op X1 y) (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq28210 X0 X1
       have i₂ := eq2818 X0 (M.op (M.op X1 y) sF0)
       grind)
    | exact superpose eq2818 eq28210
    | exact resolve eq28210 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28210
  have eq28311 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x y) X1) X0) x) y) = (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op X1 y))))) := by
    intro X0 X1
    first
    | exact superpose eq16226 eq28221
    | exact resolve eq28221 eq16226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16226 eq28221
  have eq28372 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x y) X1) X0) x) y) = (M.op (M.op x y) (M.op y (M.op X0 (M.op x (M.op y (M.op X1 y)))))) := by
    intro X0 X1
    first
    | exact superpose eq1638 eq28311
    | exact resolve eq28311 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28311
  have eq28409 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x y) X1) X0) x) y) = (M.op (M.op x y) (M.op x (M.op y (M.op X0 (M.op y (M.op X1 y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq28372 x X1
       have i₂ := eq27242 (M.op y (M.op X1 y)) sF0 x
       grind)
    | exact superpose eq27242 eq28372
    | exact resolve eq28372 eq27242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27242 eq28372
  have eq28429 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x y) X1) X0) x) y) = (M.op (M.op x y) (M.op x (M.op X0 (M.op X1 y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28409 X0 X1
       have i₂ := eq7926 X0 y (M.op X1 y) x
       grind)
    | exact superpose eq7926 eq28409
    | exact resolve eq28409 eq7926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28409
  have eq28442 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op X1 (M.op x y)))) = (M.op (M.op x y) (M.op x (M.op X0 (M.op X1 y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28429 x X1
       have i₂ := eq23491 sF0 X1 x
       grind)
    | exact superpose eq23491 eq28429
    | exact resolve eq28429 eq23491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23491 eq28429
  have eq28668 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) (M.op X0 (σ y))) y) X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq7377 eq7807
    | exact resolve eq7807 eq7377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7377
  have eq28752 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op (M.op (M.op X0 x) y) X1) X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7807 eq4386
    | exact resolve eq4386 eq7807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7807
  have eq28823 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) y) (M.op (σ y) X0)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq28668 X1 X1
       have i₂ := eq7891 sF2 X1 sF3 y
       grind)
    | exact superpose eq7891 eq28668
    | exact resolve eq28668 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28668
  have eq28865 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) y) (M.op x y)) (M.op (σ y) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28823 X0 x
       have i₂ := eq7799 (M.op sF2 y) (M.op sF3 X0) x sF0
       grind)
    | (have i₁ := eq28823 X0 x
       have i₂ := eq7799 (M.op sF2 y) sF0 (M.op sF3 X0) x
       grind)
    | exact superpose eq7799 eq28823
    | exact resolve eq28823 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28823
  have eq28894 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) y) x) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq17551 eq28865
    | exact resolve eq28865 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28865
  have eq28914 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) x) y) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28894 X0 X1
       have i₂ := eq4386 sF2 y x
       grind)
    | (have i₁ := eq28894 X0 X1
       have i₂ := eq4386 sF2 x y
       grind)
    | exact superpose eq4386 eq28894
    | exact resolve eq28894 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28894
  have eq28927 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq2915 eq28914
    | exact resolve eq28914 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28914
  have eq28934 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op y (σ y)))) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq2936 eq28927
    | exact resolve eq28927 eq2936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28927
  have eq29865 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op (M.op (M.op (M.op X0 x) y) x) (M.op X1 (M.op x y))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq4316 eq12790
    | exact resolve eq12790 eq4316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29874 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) y) = (M.op (M.op (M.op X0 x) (M.op X2 X1)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12790 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq1693 X0 X1 X2
       grind)
    | exact superpose eq1693 eq12790
    | exact resolve eq12790 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12790
  have eq30065 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) y) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29874 X0 X2 X1
       have i₂ := eq7891 (M.op X0 x) X1 X2 sF0
       grind)
    | exact superpose eq7891 eq29874
    | exact resolve eq29874 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29874
  have eq30074 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 x) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq28752 eq29865
    | exact resolve eq29865 eq28752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28752 eq29865
  have eq30179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) y) = (M.op (M.op (M.op X0 x) x) (M.op y (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq17551 eq30065
    | exact resolve eq30065 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30065
  have eq33843 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op (M.op x y) X0) y) X1) := by
    intro X0 X1
    first
    | exact superpose eq16414 eq1803
    | exact resolve eq1803 eq16414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16414
  have eq34551 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16501 x
       have i₂ := eq135 x
       grind)
    | exact superpose eq135 eq16501
    | exact resolve eq16501 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16501
  have eq34600 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq34551
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34551
    | exact resolve eq34551 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34551
  have eq34610 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq2915 eq34600
    | exact resolve eq34600 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34600
  have eq34618 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq27650 eq34610
    | exact resolve eq34610 eq27650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27650 eq34610
  have eq34623 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x))))) := by
    first
    | exact superpose eq10205 eq34618
    | exact resolve eq34618 eq10205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34618
  have eq34627 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq24593 eq34623
    | exact resolve eq34623 eq24593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24593 eq34623
  have eq34631 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq34627
       have i₂ := eq1803 sF4 sF4 sF2
       grind)
    | exact superpose eq1803 eq34627
    | exact resolve eq34627 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34627
  have eq34666 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq34631 eq7792
    | exact resolve eq7792 eq34631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7792
  have eq34672 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq34631 eq236
    | exact resolve eq236 eq34631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34686 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq34631 eq1693
    | exact resolve eq1693 eq34631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34700 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq34631 eq4386
    | exact resolve eq4386 eq34631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34631
  have eq34711 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq34700 eq18515
    | exact resolve eq18515 eq34700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18515
  have eq34737 : (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq34672
       have i₂ := eq236 sF1
       grind)
    | exact superpose eq236 eq34672
    | exact resolve eq34672 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34672
  have eq34742 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op (σ x) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1639 eq34666
    | exact resolve eq34666 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34666
  have eq34766 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq37 eq34737
    | exact resolve eq34737 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq34737
  have eq34769 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34742 X0
       have i₂ := eq1661 sF2 (M.op (M.op sF1 sF1) X0) sF3
       grind)
    | exact superpose eq1661 eq34742
    | exact resolve eq34742 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34742
  have eq34784 : (k x (M.op (M.op x y) (M.op x y))) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq34766 eq4767
    | exact resolve eq4767 eq34766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767
  have eq34807 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq2137 eq34784
    | exact resolve eq34784 eq2137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137 eq34784
  have eq35015 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq34711 eq409
    | exact resolve eq409 eq34711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34711
  have eq35112 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (M.op (σ (M.op x y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq35015 eq409
    | exact resolve eq409 eq35015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35127 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (σ x)) (M.op x y))) := by
    first
    | exact superpose eq35015 eq4316
    | exact resolve eq4316 eq35015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4316 eq35015
  have eq35142 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op x y)))) := by
    first
    | (have i₁ := eq35127
       have i₂ := eq1643 sF1 sF1 sF2 sF0
       grind)
    | exact superpose eq1643 eq35127
    | exact resolve eq35127 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35127
  have eq35155 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq35112 x
       have i₂ := eq1643 sF1 (M.op sF1 x) sF2 x
       grind)
    | exact superpose eq1643 eq35112
    | exact resolve eq35112 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35112
  have eq35163 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op x y) (σ x)))) := by
    first
    | (have i₁ := eq35142
       have i₂ := eq1802 sF1 sF2 sF0 sF1
       grind)
    | (have i₁ := eq35142
       have i₂ := eq1802 sF1 sF0 sF2 sF1
       grind)
    | exact superpose eq1802 eq35142
    | exact resolve eq35142 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35142
  have eq35178 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op (M.op x y) (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | (have i₁ := eq35163
       have i₂ := eq3367 sF1 sF2 sF1 sF0
       grind)
    | (have i₁ := eq35163
       have i₂ := eq3367 sF0 sF2 sF1 sF1
       grind)
    | exact superpose eq3367 eq35163
    | exact resolve eq35163 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35163
  have eq35202 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) := by
    first
    | exact superpose eq1638 eq35178
    | exact resolve eq35178 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35178
  have eq35217 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) = (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) := by
    first
    | exact superpose eq2915 eq35202
    | exact resolve eq35202 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35202
  have eq35243 : (M.op (M.op (σ x) (σ y)) (M.op x (M.op y (σ y)))) = (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) := by
    first
    | exact superpose eq2936 eq35217
    | exact resolve eq35217 eq2936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936 eq35217
  have eq35269 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq35243 eq28934
    | exact resolve eq28934 eq35243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28934 eq35243
  have eq35663 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X0)) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq34766 eq3488
    | exact resolve eq3488 eq34766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488 eq34766
  have eq35687 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) x) (M.op y (M.op X0 X0))) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq17551 eq35663
    | exact resolve eq35663 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35663
  have eq35706 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) x) y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq35687 x
       have i₂ := eq1661 y (M.op sF0 x) x
       grind)
    | exact superpose eq1661 eq35687
    | exact resolve eq35687 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35687
  have eq35716 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq33843 eq35706
    | exact resolve eq35706 eq33843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33843 eq35706
  have eq37168 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) y) (M.op X0 (M.op (σ x) (σ y)))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq34686 eq13390
    | exact resolve eq13390 eq34686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34686
  have eq37169 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) y) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq37168 x
       have i₂ := eq7891 (M.op sF4 y) x sF4 sF0
       grind)
    | exact superpose eq7891 eq37168
    | exact resolve eq37168 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37168
  have eq37244 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) y) x) (M.op y (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq17551 eq37169
    | exact resolve eq37169 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37169
  have eq37307 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op y (M.op (σ y) y))) (M.op y (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq35269 eq37244
    | exact resolve eq37244 eq35269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35269 eq37244
  have eq37361 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op y (M.op (σ y) y))) (M.op y (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq1639 eq37307
    | exact resolve eq37307 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37307
  have eq37404 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (σ y)) (M.op y (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq37361 X0
       have i₂ := eq534 (M.op sF1 (M.op x (M.op y (M.op sF1 sF2)))) y sF3
       grind)
    | exact superpose eq534 eq37361
    | exact resolve eq37361 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37361
  have eq37441 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (M.op (M.op y (M.op (σ (M.op x y)) (σ x))) x)) (M.op y (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq37404 X0
       have i₂ := eq7891 sF1 x (M.op y (M.op sF1 sF2)) sF3
       grind)
    | exact superpose eq7891 eq37404
    | exact resolve eq37404 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37404
  have eq37465 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (M.op y (M.op (M.op (σ (M.op x y)) (σ x)) x))) (M.op y (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq37441 X0
       have i₂ := eq1643 y (M.op sF1 sF3) (M.op sF1 sF2) x
       grind)
    | exact superpose eq1643 eq37441
    | exact resolve eq37441 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37441
  have eq37485 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (M.op y (M.op x (M.op (σ (M.op x y)) (σ x))))) (M.op y (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq37465 X0
       have i₂ := eq1802 (M.op sF1 sF3) (M.op sF1 sF2) x y
       grind)
    | (have i₁ := eq37465 X0
       have i₂ := eq1802 (M.op sF1 sF3) x (M.op sF1 sF2) y
       grind)
    | exact superpose eq1802 eq37465
    | exact resolve eq37465 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37465
  have eq37492 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op y (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq37485 X0
       have i₂ := eq3367 y (M.op sF1 sF2) (M.op sF1 sF3) x
       grind)
    | (have i₁ := eq37485 X0
       have i₂ := eq3367 x (M.op sF1 sF2) (M.op sF1 sF3) y
       grind)
    | exact superpose eq3367 eq37485
    | exact resolve eq37485 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37485
  have eq37498 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op y (M.op (σ x) (M.op (σ y) X0)))) = (M.op (M.op (M.op (σ (M.op x y)) x) (σ (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq37492 x
       have i₂ := eq7799 sF1 sF1 x x
       grind)
    | (have i₁ := eq37492 x
       have i₂ := eq7799 sF1 x sF1 x
       grind)
    | exact superpose eq7799 eq37492
    | exact resolve eq37492 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37492
  have eq38183 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) X1) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq34700 eq1693
    | exact resolve eq1693 eq34700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34700
  have eq38222 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq38183 x x
       have i₂ := eq4468 sF1 sF1 x sF4 x
       grind)
    | exact superpose eq4468 eq38183
    | exact resolve eq38183 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38183
  have eq38274 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) X0)))) := by
    intro X0
    first
    | exact superpose eq1639 eq38222
    | exact resolve eq38222 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639 eq38222
  have eq38299 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq10205 eq38274
    | exact resolve eq38274 eq10205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38274
  have eq38423 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | exact superpose eq38299 eq2915
    | exact resolve eq2915 eq38299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq38474 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq38423 X0 X1
       have i₂ := eq1803 sF2 (M.op X0 X1) sF3
       grind)
    | exact superpose eq1803 eq38423
    | exact resolve eq38423 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38423
  have eq38991 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) X0) y) (σ x)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq34769 eq13390
    | exact resolve eq13390 eq34769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13390 eq34769
  have eq38992 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) X0) y) (M.op x y)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq38991 X0
       have i₂ := eq4386 (M.op (M.op sF2 X0) y) sF2 sF0
       grind)
    | (have i₁ := eq38991 X0
       have i₂ := eq4386 (M.op (M.op sF2 X0) y) sF0 sF2
       grind)
    | exact superpose eq4386 eq38991
    | exact resolve eq38991 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38991
  have eq39048 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) X0) y) x) (M.op y (σ x))) := by
    intro X0
    first
    | exact superpose eq17551 eq38992
    | exact resolve eq38992 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38992
  have eq39081 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) X0) x) (M.op y (σ x))) y) := by
    intro X0
    first
    | (have i₁ := eq39048 X0
       have i₂ := eq7799 (M.op sF2 X0) y x (M.op y sF2)
       grind)
    | (have i₁ := eq39048 X0
       have i₂ := eq7799 (M.op sF2 X0) (M.op y sF2) y x
       grind)
    | exact superpose eq7799 eq39048
    | exact resolve eq39048 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39048
  have eq39102 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) X0) x) x) (M.op y (M.op x (M.op y (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq39081 X0
       have i₂ := eq30179 (M.op sF2 X0) x (M.op y sF2)
       grind)
    | exact superpose eq30179 eq39081
    | exact resolve eq39081 eq30179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30179 eq39081
  have eq39118 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (M.op (M.op (M.op (σ x) X0) x) x) (M.op x (M.op y (M.op y (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq39102 X0
       have i₂ := eq3367 y (M.op y sF2) (M.op (M.op (M.op sF2 X0) x) x) x
       grind)
    | (have i₁ := eq39102 X0
       have i₂ := eq3367 x (M.op y sF2) (M.op (M.op (M.op sF2 X0) x) x) y
       grind)
    | exact superpose eq3367 eq39102
    | exact resolve eq39102 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39102
  have eq39128 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (σ x) (M.op (M.op y (M.op y (σ x))) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq39118 x
       have i₂ := eq4468 sF2 x x (M.op y (M.op y sF2)) x
       grind)
    | exact superpose eq4468 eq39118
    | exact resolve eq39118 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468 eq39118
  have eq39135 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (σ x) (M.op y (M.op (M.op y (σ x)) (M.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq39128 X0
       have i₂ := eq1643 y sF2 (M.op y sF2) (M.op X0 x)
       grind)
    | exact superpose eq1643 eq39128
    | exact resolve eq39128 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39128
  have eq39139 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (σ x) (M.op y (M.op y (M.op (σ x) (M.op X0 x))))) := by
    intro X0
    first
    | (have i₁ := eq39135 X0
       have i₂ := eq1643 y y sF2 (M.op X0 x)
       grind)
    | exact superpose eq1643 eq39135
    | exact resolve eq39135 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39135
  have eq39144 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (σ x) (M.op (σ x) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq39139 X0
       have i₂ := eq1803 sF2 (M.op sF2 (M.op X0 x)) y
       grind)
    | exact superpose eq1803 eq39139
    | exact resolve eq39139 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39139
  have eq39147 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) x) = (M.op (σ x) (M.op x (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq39144 x
       have i₂ := eq3370 sF2 sF2 x x
       grind)
    | (have i₁ := eq39144 x
       have i₂ := eq3370 x sF2 sF2 x
       grind)
    | exact superpose eq3370 eq39144
    | exact resolve eq39144 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39144
  have eq39149 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) x) (σ (M.op x y))) X0) = (M.op (σ x) (M.op x (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq39147 x
       have i₂ := eq7799 sF1 sF1 x x
       grind)
    | (have i₁ := eq39147 x
       have i₂ := eq7799 sF1 x sF1 x
       grind)
    | exact superpose eq7799 eq39147
    | exact resolve eq39147 eq7799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7799 eq39147
  have eq39151 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op y (M.op (σ x) (M.op (σ y) X0)))) = (M.op (σ x) (M.op x (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq39149 eq37498
    | exact resolve eq37498 eq39149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37498 eq39149
  have eq46341 : ∀ X0 : G, (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq34807
       have i₂ := eq3467 X0 sF2 sF2
       grind)
    | (have i₁ := eq34807
       have i₂ := eq3467 sF2 sF2 x
       grind)
    | exact superpose eq3467 eq34807
    | exact resolve eq34807 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46342 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x x))) := by
    first
    | exact superpose eq34807 eq11
    | exact resolve eq11 eq34807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34807
  have eq46512 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq46342
       have i₂ := eq3467 X0 x x
       grind)
    | (have i₁ := eq46342
       have i₂ := eq3467 x x X0
       grind)
    | exact superpose eq3467 eq46342
    | exact resolve eq46342 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467 eq46342
  have eq46833 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) (M.op X1 y)) (M.op X3 (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq17459 eq398
    | exact resolve eq398 eq17459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq46870 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 x) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1796 (M.op X0 x) X1 y
       have i₂ := eq17459 X0 X1
       grind)
    | (have i₁ := eq1796 (M.op X0 X1) x y
       have i₂ := eq17459 X0 X1
       grind)
    | exact superpose eq17459 eq1796
    | exact resolve eq1796 eq17459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47677 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y (M.op X0 (M.op x y)))) X1) = (M.op (M.op (M.op x X0) x) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17551 (M.op x X0) X1
       have i₂ := eq2818 X0 sF0
       grind)
    | exact superpose eq2818 eq17551
    | exact resolve eq17551 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47679 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op X1 y)) X2) = (M.op (M.op (M.op X0 X1) x) (M.op y X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq17459 eq17551
    | exact resolve eq17551 eq17459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17459
  have eq48051 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y (M.op X0 (M.op x y)))) X1) = (M.op (M.op (M.op x y) (M.op y (M.op X0 x))) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47677 X0 X1
       have i₂ := eq2818 X0 x
       grind)
    | exact superpose eq2818 eq47677
    | exact resolve eq47677 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47677
  have eq48184 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y (M.op X0 (M.op x y)))) X1) = (M.op (M.op (M.op x y) (M.op x (M.op y X0))) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48051 x X1
       have i₂ := eq3370 y sF0 x x
       grind)
    | (have i₁ := eq48051 x X1
       have i₂ := eq3370 x sF0 y x
       grind)
    | exact superpose eq3370 eq48051
    | exact resolve eq48051 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48051
  have eq48279 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x (M.op y X0))) (M.op y X1)) = (M.op (M.op (M.op x y) (M.op x (M.op y (M.op X0 y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq28442 eq48184
    | exact resolve eq48184 eq28442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28442 eq48184
  have eq48349 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x (M.op y X0))) (M.op y X1)) = (M.op (M.op (M.op x y) (M.op x X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48279 X0 X1
       have i₂ := eq534 x y X0
       grind)
    | exact superpose eq534 eq48279
    | exact resolve eq48279 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48279
  have eq54210 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op X0 (M.op X2 (M.op X1 (M.op x y)))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq23641 eq1800
    | exact resolve eq1800 eq23641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23641
  have eq54212 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x (M.op y X1))) X2) = (M.op (M.op X0 (M.op X2 X1)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1638 eq1800
    | exact resolve eq1800 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54478 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X4) = (M.op (M.op X0 (M.op X4 X3)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1796 (M.op X0 (M.op X4 X3)) X1 X2
       have i₂ := eq1800 X4 X0 (M.op X1 X2) X3
       grind)
    | (have i₁ := eq1796 (M.op X0 (M.op X4 X3)) X1 X2
       have i₂ := eq1800 (M.op X1 X2) X0 X4 X3
       grind)
    | exact superpose eq1800 eq1796
    | exact resolve eq1796 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54572 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X0 (M.op X4 X3)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54478 X0 X1 X2 X3 X4
       have i₂ := eq1643 X1 X0 X2 X3
       grind)
    | exact superpose eq1643 eq54478
    | exact resolve eq54478 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54478
  have eq54919 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x (M.op y X1))) X2) = (M.op (M.op X0 (M.op x y)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54212 X0 X2 X1
       have i₂ := eq7891 X0 X1 X2 sF0
       grind)
    | exact superpose eq7891 eq54212
    | exact resolve eq54212 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54212
  have eq54921 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op x y)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54210 X0 X1 X1
       have i₂ := eq7891 X0 X1 (M.op X1 sF0) x
       grind)
    | exact superpose eq7891 eq54210
    | exact resolve eq54210 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54210
  have eq55514 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op x (M.op y X1))) X2) = (M.op (M.op X0 x) (M.op y (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq17551 eq54919
    | exact resolve eq54919 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54919
  have eq55515 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54921 X0 X0 x
       have i₂ := eq1643 X0 (M.op X0 x) sF0 x
       grind)
    | exact superpose eq1643 eq54921
    | exact resolve eq54921 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54921
  have eq56009 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) x) (M.op y (M.op (M.op (σ (M.op x y)) (σ x)) (M.op y (M.op (σ x) (M.op (σ y) X0)))))) := by
    intro X0
    first
    | (have i₁ := eq39151 X0
       have i₂ := eq55514 (M.op sF1 sF3) (M.op sF1 sF2) (M.op y (M.op sF2 (M.op sF3 X0)))
       grind)
    | exact superpose eq55514 eq39151
    | exact resolve eq39151 eq55514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39151
  have eq56010 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x X0)) X1) = (M.op (M.op (M.op x y) x) (M.op y (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48349 X1 X1
       have i₂ := eq55514 sF0 X1 (M.op y X1)
       grind)
    | exact superpose eq55514 eq48349
    | exact resolve eq48349 eq55514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48349 eq55514
  have eq56028 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op X0 x) (M.op X1 (M.op x (M.op y X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1638 eq55515
    | exact resolve eq55515 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55515
  have eq56376 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op X0 X1)) = (M.op (M.op (M.op x y) (M.op x X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56010 X0 x
       have i₂ := eq7926 X0 y x (M.op sF0 x)
       grind)
    | exact superpose eq7926 eq56010
    | exact resolve eq56010 eq7926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56010
  have eq56377 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) (M.op (σ y) y)) (M.op (M.op (σ (M.op x y)) (σ x)) (M.op y (M.op (σ x) (M.op (σ y) X0))))) := by
    intro X0
    first
    | (have i₁ := eq56009 X0
       have i₂ := eq47679 sF1 sF3 (M.op (M.op sF1 sF2) (M.op y (M.op sF2 (M.op sF3 X0))))
       grind)
    | exact superpose eq47679 eq56009
    | exact resolve eq56009 eq47679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47679 eq56009
  have eq56452 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op x (M.op y (M.op X3 (M.op x y)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq46833 X0 X1 X2 X3
       have i₂ := eq56028 (M.op X0 x) X1 (M.op X3 sF0)
       grind)
    | exact superpose eq56028 eq46833
    | exact resolve eq46833 eq56028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46833
  have eq56672 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op (σ y) (M.op x (M.op y (M.op (M.op (σ (M.op x y)) (σ x)) (M.op y (M.op (σ x) (M.op (σ y) X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq56377 X0
       have i₂ := eq56028 (M.op sF1 x) sF3 (M.op (M.op sF1 sF2) (M.op y (M.op sF2 (M.op sF3 X0))))
       grind)
    | exact superpose eq56028 eq56377
    | exact resolve eq56377 eq56028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56028 eq56377
  have eq56727 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op x (M.op x (M.op y (M.op X3 y)))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq22296 eq56452
    | exact resolve eq56452 eq22296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22296 eq56452
  have eq56893 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op (σ y) (M.op y (M.op (M.op (σ (M.op x y)) (σ x)) (M.op y (M.op (σ x) (M.op (σ y) X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq56672 X0
       have i₂ := eq3367 sF3 (M.op y (M.op (M.op sF1 sF2) (M.op y (M.op sF2 (M.op sF3 X0))))) (M.op (M.op sF1 x) x) x
       grind)
    | (have i₁ := eq56672 X0
       have i₂ := eq3367 x (M.op y (M.op (M.op sF1 sF2) (M.op y (M.op sF2 (M.op sF3 X0))))) (M.op (M.op sF1 x) x) sF3
       grind)
    | exact superpose eq3367 eq56672
    | exact resolve eq56672 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56672
  have eq56931 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op y (M.op X3 y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56727 X0 X1 X2 X3
       have i₂ := eq1803 X1 (M.op y (M.op X3 y)) x
       grind)
    | exact superpose eq1803 eq56727
    | exact resolve eq56727 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56727
  have eq57056 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op y (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ x)) (M.op y (M.op (σ x) (M.op (σ y) X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq56893 X0
       have i₂ := eq3367 sF3 (M.op (M.op sF1 sF2) (M.op y (M.op sF2 (M.op sF3 X0)))) x y
       grind)
    | (have i₁ := eq56893 X0
       have i₂ := eq3367 y (M.op (M.op sF1 sF2) (M.op y (M.op sF2 (M.op sF3 X0)))) x sF3
       grind)
    | exact superpose eq3367 eq56893
    | exact resolve eq56893 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56893
  have eq57076 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56931 X0 X1 X2 X3
       have i₂ := eq534 X1 y X3
       grind)
    | exact superpose eq534 eq56931
    | exact resolve eq56931 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56931
  have eq57125 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op y (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (M.op y (M.op (σ x) (M.op (σ y) X0))))))))) := by
    intro X0
    first
    | (have i₁ := eq57056 X0
       have i₂ := eq1643 sF1 sF3 sF2 (M.op y (M.op sF2 (M.op sF3 X0)))
       grind)
    | exact superpose eq1643 eq57056
    | exact resolve eq57056 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57056
  have eq57188 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op (σ (M.op x y)) (M.op y (M.op (σ y) (M.op (σ x) (M.op y (M.op (σ x) (M.op (σ y) X0))))))))) := by
    intro X0
    first
    | exact superpose eq25837 eq57125
    | exact resolve eq57125 eq25837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25837 eq57125
  have eq57236 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op y (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ x) (M.op y (M.op (σ x) (M.op (σ y) X0))))))))) := by
    intro X0
    first
    | (have i₁ := eq57188 X0
       have i₂ := eq3367 sF1 (M.op sF3 (M.op sF2 (M.op y (M.op sF2 (M.op sF3 X0))))) x y
       grind)
    | (have i₁ := eq57188 X0
       have i₂ := eq3367 y (M.op sF3 (M.op sF2 (M.op y (M.op sF2 (M.op sF3 X0))))) x sF1
       grind)
    | exact superpose eq3367 eq57188
    | exact resolve eq57188 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57188
  have eq57277 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op y (M.op (σ x) (M.op (σ y) X0))))))))) := by
    intro X0
    first
    | (have i₁ := eq57236 X0
       have i₂ := eq3367 sF3 (M.op y (M.op sF2 (M.op sF3 X0))) sF1 sF2
       grind)
    | (have i₁ := eq57236 X0
       have i₂ := eq3367 sF2 (M.op y (M.op sF2 (M.op sF3 X0))) sF1 sF3
       grind)
    | exact superpose eq3367 eq57236
    | exact resolve eq57236 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367 eq57236
  have eq57314 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op y (M.op (σ (M.op x y)) (M.op y (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))))))))) := by
    intro X0
    first
    | exact superpose eq10205 eq57277
    | exact resolve eq57277 eq10205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57277
  have eq57340 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op (σ y) X0))))))) := by
    intro X0
    first
    | (have i₁ := eq57314 X0
       have i₂ := eq7926 sF1 y (M.op sF2 (M.op sF3 (M.op sF2 (M.op sF3 X0)))) x
       grind)
    | exact superpose eq7926 eq57314
    | exact resolve eq57314 eq7926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57314
  have eq57361 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))))))) := by
    intro X0
    first
    | exact superpose eq10205 eq57340
    | exact resolve eq57340 eq10205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10205 eq57340
  have eq57379 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ y) X0))))) := by
    intro X0
    first
    | (have i₁ := eq57361 X0
       have i₂ := eq1803 sF1 (M.op sF3 (M.op sF3 X0)) sF2
       grind)
    | exact superpose eq1803 eq57361
    | exact resolve eq57361 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57361
  have eq57391 : ∀ X0 : G, (M.op (σ x) (M.op x (M.op (σ x) X0))) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op (σ (M.op x y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq57379 x
       have i₂ := eq1803 sF1 x sF3
       grind)
    | exact superpose eq1803 eq57379
    | exact resolve eq57379 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57379
  have eq57612 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1802 X3 X1 (M.op X0 X2) X4
       have i₂ := eq4386 X0 X2 X1
       grind)
    | (have i₁ := eq1802 X3 X1 (M.op X0 X2) X4
       have i₂ := eq4386 X0 X1 X2
       grind)
    | exact superpose eq4386 eq1802
    | exact resolve eq1802 eq4386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57955 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op X2 X3))) = (M.op (M.op X0 x) (M.op y (M.op X1 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17551 X0 (M.op x (M.op X1 X2))
       have i₂ := eq1802 (M.op X0 sF0) X1 X2 x
       grind)
    | (have i₁ := eq17551 X0 (M.op x (M.op X2 X1))
       have i₂ := eq1802 (M.op X0 sF0) X1 X2 x
       grind)
    | exact superpose eq1802 eq17551
    | exact resolve eq17551 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57968 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op X0 (M.op X2 (M.op X4 X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4386 X0 X1 (M.op X2 (M.op X4 X3))
       have i₂ := eq1802 (M.op X0 X1) X4 X3 X2
       grind)
    | (have i₁ := eq4386 X0 X1 (M.op X2 (M.op X4 X3))
       have i₂ := eq1802 (M.op X0 X1) X3 X4 X2
       grind)
    | exact superpose eq1802 eq4386
    | exact resolve eq4386 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802 eq4386
  have eq58035 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 x) (M.op y (M.op X1 (M.op X2 X3)))) = (M.op (M.op X0 x) (M.op y (M.op X1 (M.op X3 X2)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq17551 eq57955
    | exact resolve eq57955 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57955
  have eq58281 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) = (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57612 X1 X0 X2 X3 X4
       have i₂ := eq1643 X1 X4 X0 X2
       grind)
    | exact superpose eq1643 eq57612
    | exact resolve eq57612 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57612
  have eq61058 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq21116 eq1803
    | exact resolve eq1803 eq21116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21116
  have eq66551 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x (M.op X0 y)) X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq26423 eq3469
    | exact resolve eq3469 eq26423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26423
  have eq66692 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) (M.op y (M.op (M.op X0 y) X1))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66551 X0 X1 X2
       have i₂ := eq2818 (M.op X0 y) X1
       grind)
    | exact superpose eq2818 eq66551
    | exact resolve eq66551 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66551
  have eq66930 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) (M.op (M.op X0 y) X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq66692 X0 X1 x
       have i₂ := eq6560 sF0 (M.op (M.op X0 y) X1) y x
       grind)
    | exact superpose eq6560 eq66692
    | exact resolve eq66692 eq6560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6560 eq66692
  have eq67132 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) (M.op y X1)) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq66930 X0 x
       have i₂ := eq1800 (M.op X0 y) sF0 y x
       grind)
    | (have i₁ := eq66930 X0 x
       have i₂ := eq1800 y sF0 (M.op X0 y) x
       grind)
    | exact superpose eq1800 eq66930
    | exact resolve eq66930 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66930
  have eq68812 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) y) = (M.op (M.op (M.op x y) (M.op y (M.op X0 x))) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq30074 (M.op x X0) X1
       have i₂ := eq2818 X0 x
       grind)
    | exact superpose eq2818 eq30074
    | exact resolve eq30074 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30074
  have eq69129 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) y) = (M.op (M.op (M.op x y) (M.op x (M.op y X0))) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq68812 x X1
       have i₂ := eq3370 y sF0 x x
       grind)
    | (have i₁ := eq68812 x X1
       have i₂ := eq3370 x sF0 y x
       grind)
    | exact superpose eq3370 eq68812
    | exact resolve eq68812 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370 eq68812
  have eq69376 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) y) = (M.op (M.op (M.op x y) x) (M.op (M.op y X0) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq56376 eq69129
    | exact resolve eq69129 eq56376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56376 eq69129
  have eq69578 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) y) = (M.op (M.op (M.op x y) x) (M.op y (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq69376 x X1
       have i₂ := eq1643 y (M.op sF0 x) x (M.op X1 sF0)
       grind)
    | exact superpose eq1643 eq69376
    | exact resolve eq69376 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69376
  have eq69727 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y (M.op X0 X1))) y) = (M.op (M.op (M.op x y) x) (M.op y (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq69578 X0 X1
       have i₂ := eq2818 X0 X1
       grind)
    | exact superpose eq2818 eq69578
    | exact resolve eq69578 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69578
  have eq69840 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y X1)) (M.op X0 y)) = (M.op (M.op (M.op x y) x) (M.op y (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq69727 x x
       have i₂ := eq54572 sF0 y x x y
       grind)
    | exact superpose eq54572 eq69727
    | exact resolve eq69727 eq54572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54572 eq69727
  have eq69917 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) x) (M.op y (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq67132 eq69840
    | exact resolve eq69840 eq67132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67132 eq69840
  have eq79236 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) X4) X5) = (M.op (M.op (M.op X0 (M.op X1 X2)) X3) (M.op X1 (M.op X5 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2180 (M.op X0 (M.op X3 X2)) X4 X5 X1
       have i₂ := eq1800 X3 X0 X1 X2
       grind)
    | (have i₁ := eq2180 (M.op X0 (M.op X3 X2)) X4 X5 X1
       have i₂ := eq1800 X1 X0 X3 X2
       grind)
    | exact superpose eq1800 eq2180
    | exact resolve eq2180 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800 eq2180
  have eq95479 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2207 X1 X3 X0 (M.op X2 X3)
       have i₂ := eq534 X0 X3 X2
       grind)
    | exact superpose eq534 eq2207
    | exact resolve eq2207 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95503 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2207 X2 X3 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq3469 X0 X1 X3
       grind)
    | exact superpose eq3469 eq2207
    | exact resolve eq2207 eq3469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95871 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) X4) X4) = (M.op (M.op (M.op X0 X1) X2) (M.op X1 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3567 (M.op X0 (M.op X3 X2)) X4 (M.op X1 X3)
       have i₂ := eq2207 X1 X3 X0 X2
       grind)
    | exact superpose eq2207 eq3567
    | exact resolve eq3567 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207 eq3567
  have eq95896 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 x) x) (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X2) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95871 X0 X1 X2 X3 x
       have i₂ := eq7383 X0 (M.op X3 X2) x
       grind)
    | exact superpose eq7383 eq95871
    | exact resolve eq95871 eq7383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95871
  have eq106201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq361
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq361
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq361 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq106231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106201
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106201
    | exact resolve eq106201 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106201
  have eq106240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq106231
    | exact resolve eq106231 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106231
  have eq106247 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq106240
       have r₂ := eq27
       grind)
    | exact resolve eq106240 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106240
  have eq106254 : (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106247
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106247
    | exact resolve eq106247 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106247
  have eq106255 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106254
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106254
    | exact resolve eq106254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106254
  have eq111408 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op X0 x) x) X2) X4) (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1908 (M.op X0 X1) X1 X2 X4 X3
       have i₂ := eq3196 X0 X1
       grind)
    | (have i₁ := eq1908 (M.op X0 x) x X2 X3 X4
       have i₂ := eq3196 X0 X1
       grind)
    | exact superpose eq3196 eq1908
    | exact resolve eq1908 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196
  have eq111790 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 (M.op X2 X4)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq409 (M.op (M.op (M.op X0 X3) X1) X4) (M.op X3 (M.op X2 X4)) X5
       have i₂ := eq1908 X0 X3 X1 X4 X2
       grind)
    | exact superpose eq1908 eq409
    | exact resolve eq409 eq1908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111792 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X4) X1) X5)) = (M.op X3 (M.op (M.op X4 (M.op X2 X5)) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq534 X3 (M.op X4 (M.op X2 X5)) (M.op (M.op (M.op X0 X4) X1) X5)
       have i₂ := eq1908 X0 X4 X1 X5 X2
       grind)
    | exact superpose eq1908 eq534
    | exact resolve eq534 eq1908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq111841 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X4) X1) X5)) = (M.op X3 (M.op X4 (M.op (M.op X2 X5) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq111792 X0 X1 X2 X3 X4 X5
       have i₂ := eq1643 X4 X3 (M.op X2 X5) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq1643 eq111792
    | exact resolve eq111792 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111792
  have eq111843 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op (M.op X1 X2) (M.op X3 (M.op X2 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq111790 X0 X1 X2 X3 X4 x
       have i₂ := eq57076 X0 (M.op X1 X2) x (M.op X3 (M.op X2 X4))
       grind)
    | exact superpose eq57076 eq111790
    | exact resolve eq111790 eq57076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111790
  have eq112172 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 (M.op X2 X4)) (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq111408 X0 X1 X2 X3 X4
       have i₂ := eq95503 X0 x X2 X4
       grind)
    | exact superpose eq95503 eq111408
    | exact resolve eq111408 eq95503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95503 eq111408
  have eq112229 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X0 X4) X1) X5)) = (M.op X3 (M.op X4 (M.op X2 (M.op X5 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq111841 X0 X1 X2 X3 X4 X5
       have i₂ := eq1643 X2 X4 X5 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq1643 eq111841
    | exact resolve eq111841 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111841
  have eq112231 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op X2 (M.op X3 (M.op X2 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq111843 X0 X1 X2 X3 X4
       have i₂ := eq1643 X1 (M.op (M.op X0 x) x) X2 (M.op X3 (M.op X2 X4))
       grind)
    | exact superpose eq1643 eq111843
    | exact resolve eq111843 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111843
  have eq112526 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X2 (M.op X5 (M.op X0 (M.op X1 X2)))))) = (M.op X3 (M.op (M.op X0 X4) (M.op X1 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq112229 X0 X1 X2 X3 X4 X5
       have i₂ := eq1643 (M.op X0 X4) X3 X1 X5
       grind)
    | exact superpose eq1643 eq112229
    | exact resolve eq112229 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112229
  have eq112528 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq112231 X0 X1 x X3 X4
       have i₂ := eq7926 X3 x X4 X1
       grind)
    | exact superpose eq7926 eq112231
    | exact resolve eq112231 eq7926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7926 eq112231
  have eq112781 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X2 (M.op X5 (M.op X0 (M.op X1 X2)))))) = (M.op X3 (M.op X0 (M.op X4 (M.op X1 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq112526 X0 X1 X2 X3 X4 X5
       have i₂ := eq1643 X0 X3 X4 (M.op X1 X5)
       grind)
    | exact superpose eq1643 eq112526
    | exact resolve eq112526 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112526
  have eq112863 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X3) (M.op X1 (M.op X5 X4))) = (M.op (M.op (M.op X0 x) x) (M.op X4 (M.op (M.op X3 X2) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq79236 X0 X1 X2 X3 X4 X5
       have i₂ := eq112528 X0 X4 (M.op X3 X2) X5
       grind)
    | exact superpose eq112528 eq79236
    | exact resolve eq79236 eq112528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79236
  have eq113283 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X3) (M.op X1 (M.op X5 X4))) = (M.op (M.op (M.op X0 x) x) (M.op X4 (M.op X3 (M.op X2 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq112863 X0 X1 X2 X3 X4 X5
       have i₂ := eq1643 X3 X4 X2 X5
       grind)
    | exact superpose eq1643 eq112863
    | exact resolve eq112863 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112863
  have eq113586 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 x) x) (M.op X4 (M.op X3 (M.op X2 X5)))) = (M.op (M.op (M.op X0 x) x) (M.op X3 (M.op (M.op X1 X2) (M.op X1 (M.op X5 X4))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq113283 X0 X1 X2 X3 X4 X5
       have i₂ := eq112528 X0 X3 (M.op X1 X2) (M.op X1 (M.op X5 X4))
       grind)
    | exact superpose eq112528 eq113283
    | exact resolve eq113283 eq112528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112528 eq113283
  have eq113962 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 x) x) (M.op X4 (M.op X3 (M.op X2 X5)))) = (M.op (M.op (M.op X0 x) x) (M.op X3 (M.op X1 (M.op (M.op X1 X2) (M.op X5 X4))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq113586 X0 X1 X2 X3 X4 X5
       have i₂ := eq58281 (M.op X1 X2) X1 (M.op X5 X4) (M.op (M.op X0 x) x) X3
       grind)
    | (have i₁ := eq113586 X0 X1 X2 X3 X4 X5
       have i₂ := eq58281 X1 (M.op X1 X2) (M.op X5 X4) (M.op (M.op X0 x) x) X3
       grind)
    | exact superpose eq58281 eq113586
    | exact resolve eq113586 eq58281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58281 eq113586
  have eq114284 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 x) x) (M.op X4 (M.op X3 (M.op X2 X5)))) = (M.op (M.op (M.op X0 x) x) (M.op X3 (M.op X1 (M.op X1 (M.op X2 (M.op X5 X4)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq113962 X0 X1 X2 X3 X4 X5
       have i₂ := eq1643 X1 X1 X2 (M.op X5 X4)
       grind)
    | exact superpose eq1643 eq113962
    | exact resolve eq113962 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643 eq113962
  have eq114556 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 x) x) (M.op X4 (M.op X3 (M.op X2 X5)))) = (M.op (M.op (M.op X0 x) x) (M.op X3 (M.op X2 (M.op X5 X4)))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq114284 X0 x X2 X3 X4 X5
       have i₂ := eq1803 X3 (M.op X2 (M.op X5 X4)) x
       grind)
    | exact superpose eq1803 eq114284
    | exact resolve eq114284 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114284
  have eq115274 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq106255 eq1693
    | exact resolve eq1693 eq106255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106255
  have eq115313 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) (M.op X0 (σ y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq38299 eq115274
    | exact resolve eq115274 eq38299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115274
  have eq115339 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (σ y) X0)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq115313 x
       have i₂ := eq7891 sF1 sF3 x (M.op sF1 (M.op sF2 (M.op sF3 x)))
       grind)
    | exact superpose eq7891 eq115313
    | exact resolve eq115313 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7891 eq115313
  have eq115357 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35155 eq115339
    | exact resolve eq115339 eq35155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35155 eq115339
  have eq115442 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) (M.op X0 y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1693 y y X0
       have i₂ := eq115357
       grind)
    | exact superpose eq115357 eq1693
    | exact resolve eq1693 eq115357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115357
  have eq115471 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2055 eq115442
    | exact resolve eq115442 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055 eq115442
  have eq115533 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq115471 eq2168
    | exact resolve eq2168 eq115471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115539 : (τ (σ y)) = (M.op x (M.op x (τ (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq115471 eq35716
    | exact resolve eq35716 eq115471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35716 eq115471
  have eq115547 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq115539
    | exact resolve eq115539 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115539
  have eq115550 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq115533
    | (have j0 := eq115533 X0
       grind)
    | exact resolve eq115533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115533
  have eq115551 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq115547
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115547
    | exact resolve eq115547 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115547
  have eq116295 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f116295_15 : ∀ X0 : G, (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op X0 X0))) := by
      intro X0
      grind
    have f116295_16 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
      intro X0
      grind
    have f116295_25 : (M.op x (M.op x x)) ≠ (τ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y)))) := by grind
    have f116295_26 : (σ x) ≠ (σ y) := by grind
    have f116295_27 : y ≠ (M.op x y) := by grind
    have f116295_28 : x ≠ y := by grind
    have f116295_29 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y := by
      intro X0
      first
      | (have j0 := f116295_16 X0
         grind)
      | (have r₁ := f116295_16 X0
         have r₂ := f116295_26
         grind)
      | exact resolve f116295_16 f116295_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f116295_30 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y := by
      intro X0
      first
      | (have j0 := f116295_29 X0
         grind)
      | (have r₁ := f116295_29 X0
         have r₂ := f116295_27
         grind)
      | exact resolve f116295_29 f116295_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f116295_31 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
      intro X0
      first
      | (have j0 := f116295_30 X0
         grind)
      | (have r₁ := f116295_30 X0
         have r₂ := f116295_28
         grind)
      | exact resolve f116295_30 f116295_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f116295_65 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
      first
      | (have i₁ := f116295_15 (M.op (σ x) (σ y))
         have i₂ := f116295_31 (M.op (σ x) (σ y))
         grind)
      | exact superpose f116295_31 f116295_15
      | exact resolve f116295_15 f116295_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f116295_69 : False := by
      first
      | (have r₁ := f116295_65
         have r₂ := f116295_25
         grind)
      | exact resolve f116295_65 f116295_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f116295_69
  clear eq46341 eq115550
  have eq116422 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq116295
       have i₂ := eq1796 sF2 sF4 sF3
       grind)
    | (have i₁ := eq116295
       have i₂ := eq1796 sF2 sF3 sF4
       grind)
    | exact superpose eq1796 eq116295
    | exact resolve eq116295 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796 eq116295
  have eq116492 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ y))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3385 eq116422
    | exact resolve eq116422 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385 eq116422
  have eq116543 : (τ (M.op (σ x) (σ x))) = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq116492
       have i₂ := eq1661 sF2 sF2 sF3
       grind)
    | exact superpose eq1661 eq116492
    | exact resolve eq116492 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116492
  have eq116585 : (M.op (τ (σ x)) (τ (σ x))) = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq116543
       have i₂ := eq236 sF2
       grind)
    | exact superpose eq236 eq116543
    | exact resolve eq116543 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq116543
  have eq116616 : (M.op x x) = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq116585
    | exact resolve eq116585 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116585
  have eq176498 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) (M.op X0 (M.op x x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1693 x (M.op x x) X0
       have i₂ := eq116616
       grind)
    | exact superpose eq116616 eq1693
    | exact resolve eq1693 eq116616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116616
  have eq176584 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq176498 X0
       have i₂ := eq1661 X0 (M.op (M.op x x) X0) x
       grind)
    | exact superpose eq1661 eq176498
    | exact resolve eq176498 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176498
  have eq176635 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op y (M.op x X0))) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq176584 X0
       have i₂ := eq2818 x X0
       grind)
    | exact superpose eq2818 eq176584
    | exact resolve eq176584 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818 eq176584
  have eq176682 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op y (M.op X0 (M.op (M.op y (M.op x X0)) (M.op x y))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq69917 eq176635
    | exact resolve eq176635 eq69917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176635
  have eq176725 : ∀ X0 : G, x = (M.op (M.op (M.op x y) x) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op x X0)))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq176682 x
       have i₂ := eq58035 sF0 x (M.op y (M.op x x)) sF0
       grind)
    | (have i₁ := eq176682 x
       have i₂ := eq58035 sF0 x sF0 (M.op y (M.op x x))
       grind)
    | exact superpose eq58035 eq176682
    | exact resolve eq176682 eq58035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58035 eq176682
  have eq176763 : x = (M.op (M.op (M.op x y) x) (M.op y (M.op y (M.op x (M.op x y))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq176725 x
       have i₂ := eq112781 y x x (M.op sF0 x) y sF0
       grind)
    | exact superpose eq112781 eq176725
    | exact resolve eq176725 eq112781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112781 eq176725
  have eq176791 : x = (M.op (M.op (M.op x y) x) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq69917 eq176763
    | exact resolve eq176763 eq69917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69917 eq176763
  have eq177196 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) x) (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq176791 eq46870
    | exact resolve eq46870 eq176791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46870 eq176791
  have eq177223 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq177196
       have i₂ := eq3469 sF0 x y
       grind)
    | exact superpose eq3469 eq177196
    | exact resolve eq177196 eq3469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3469 eq177196
  have eq177451 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq177223 eq115551
    | exact resolve eq115551 eq177223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115551 eq177223
  have eq177519 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq177451
  have eq177570 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq177519 eq39
    | exact resolve eq39 eq177519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq177519
  have eq177616 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq177570
    | exact resolve eq177570 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq177570
  have eq177617 : y = (M.op x y) ∨ x = y := by grind
  clear eq177616
  have eq177622 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq177617 eq20
    | exact resolve eq20 eq177617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177632 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq177617 eq1292
    | exact resolve eq1292 eq177617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292 eq177617
  have eq177651 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq177632 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177632
    | (have j0 := eq177632 X0
       grind)
    | exact resolve eq177632 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177632
  have eq177652 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq177622
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq177622
    | exact resolve eq177622 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177622
  have eq177654 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq177652 eq26
    | exact resolve eq26 eq177652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177652
  have eq177758 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq177654 eq1803
    | exact resolve eq1803 eq177654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803 eq177654
  have eq177823 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2168 eq177758
    | exact resolve eq177758 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168 eq177758
  have eq179296 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op (M.op x y) y))) ∨ x = y := by
    first
    | exact superpose eq177651 eq46512
    | exact resolve eq46512 eq177651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46512
  have eq179312 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op x y)) (M.op X0 y)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq177651 eq409
    | exact resolve eq409 eq177651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179319 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op x y)) X0) (M.op X0 y)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq177651 eq1693
    | exact resolve eq1693 eq177651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693 eq177651
  have eq179512 : ∀ X1 : G, (M.op (M.op (M.op X1 x) (M.op x y)) (M.op x y)) = X1 ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq179319 x x
       have i₂ := eq12953 x sF0 x
       grind)
    | exact superpose eq12953 eq179319
    | exact resolve eq179319 eq12953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12953 eq179319
  have eq179518 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) x) (M.op y (M.op X0 y))) = X1 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq17551 eq179312
    | exact resolve eq179312 eq17551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17551 eq179312
  have eq179526 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x (M.op y y)))) ∨ x = y := by
    first
    | exact superpose eq1638 eq179296
    | exact resolve eq179296 eq1638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq179296
  have eq179595 : ∀ X1 : G, (M.op (M.op (M.op X1 x) x) x) = X1 ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq179512 x
       have i₂ := eq7383 x x sF0
       grind)
    | exact superpose eq7383 eq179512
    | exact resolve eq179512 eq7383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179512
  have eq179601 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) x) X0) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq179518 X0 X1
       have i₂ := eq534 (M.op (M.op X1 X0) x) y X0
       grind)
    | exact superpose eq534 eq179518
    | exact resolve eq179518 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq179518
  have eq179608 : (σ (M.op x x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq179526
       have i₂ := eq1661 x x y
       grind)
    | exact superpose eq1661 eq179526
    | exact resolve eq179526 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq179526
  have eq179669 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq179608
       have i₂ := eq135 x
       grind)
    | exact superpose eq135 eq179608
    | exact resolve eq179608 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179608
  have eq179710 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq179669
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq179669
    | exact resolve eq179669 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179669
  have eq195366 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) x)))) x) x) ∨ x = y := by
    first
    | exact superpose eq38299 eq179595
    | exact resolve eq179595 eq38299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38299 eq179595
  have eq195543 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) x)))) ∨ x = y := by
    first
    | (have i₁ := eq195366
       have i₂ := eq7383 sF1 (M.op sF1 (M.op sF2 (M.op sF3 x))) x
       grind)
    | exact superpose eq7383 eq195366
    | exact resolve eq195366 eq7383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7383 eq195366
  have eq195606 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op (σ (M.op x y)) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | (have i₁ := eq195543
       have i₂ := eq114556 sF1 sF3 sF2 sF1 x
       grind)
    | (have i₁ := eq195543
       have i₂ := eq114556 sF1 sF2 sF1 x sF3
       grind)
    | exact superpose eq114556 eq195543
    | exact resolve eq195543 eq114556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114556 eq195543
  have eq195644 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq57391 eq195606
    | exact resolve eq195606 eq57391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57391 eq195606
  have eq195662 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op x (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq19010 eq195644
    | exact resolve eq195644 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010 eq195644
  have eq195674 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ y))) ∨ x = y := by
    first
    | exact superpose eq61058 eq195662
    | exact resolve eq195662 eq61058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61058 eq195662
  have eq195689 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ (M.op x y)))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq177823 eq195674
    | exact resolve eq195674 eq177823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177823 eq195674
  have eq195754 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ (M.op x y)))) ∨ x = y := by grind
  clear eq195689
  have eq204745 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) x) (M.op (σ x) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq179710 eq179601
    | exact resolve eq179601 eq179710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179601 eq179710
  have eq204748 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) x) (M.op (σ x) (σ x))) ∨ x = y := by grind
  clear eq204745
  have eq204759 : (σ x) = (M.op (M.op (M.op (σ x) x) x) (M.op (σ x) x)) ∨ x = y := by
    first
    | (have i₁ := eq204748
       have i₂ := eq95896 sF2 sF2 x sF2
       grind)
    | exact superpose eq95896 eq204748
    | exact resolve eq204748 eq95896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95896 eq204748
  have eq204815 : (σ x) = (M.op (M.op (M.op (σ x) x) x) (M.op x (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq204759
       have i₂ := eq57076 sF2 x x sF2
       grind)
    | (have i₁ := eq204759
       have i₂ := eq57076 sF2 sF2 x x
       grind)
    | exact superpose eq57076 eq204759
    | exact resolve eq204759 eq57076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57076 eq204759
  have eq204869 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op x x)))) (M.op x (σ x))) ∨ x = y := by
    first
    | exact superpose eq38474 eq204815
    | exact resolve eq204815 eq38474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38474 eq204815
  have eq204919 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op x (σ x))) (M.op (σ (M.op x y)) (M.op (M.op x x) (σ x)))) ∨ x = y := by
    first
    | (have i₁ := eq204869
       have i₂ := eq57968 sF1 (M.op x sF2) sF1 (M.op x x) sF2
       grind)
    | exact superpose eq57968 eq204869
    | exact resolve eq204869 eq57968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57968 eq204869
  have eq204965 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op x (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq204919
       have i₂ := eq112172 sF1 sF1 x (M.op x x) sF2
       grind)
    | exact superpose eq112172 eq204919
    | exact resolve eq204919 eq112172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112172 eq204919
  have eq205003 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op (σ (M.op x y)) (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq204965
       have i₂ := eq95479 sF1 sF1 x (M.op x x)
       grind)
    | (have i₁ := eq204965
       have i₂ := eq95479 sF1 x sF1 (M.op x x)
       grind)
    | exact superpose eq95479 eq204965
    | exact resolve eq204965 eq95479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95479 eq204965
  have eq205026 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq205003
       have i₂ := eq2728 sF1 x x sF1
       grind)
    | exact superpose eq2728 eq205003
    | exact resolve eq205003 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728 eq205003
  have eq205531 : (σ (M.op x y)) = (M.op (σ x) (M.op x (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq205026 eq409
    | exact resolve eq409 eq205026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq205026
  have eq206234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq205531 eq195754
    | exact resolve eq195754 eq205531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195754 eq205531
  have eq206304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq206234
  have eq206359 : x = y := by
    first
    | (have r₁ := eq206304
       have r₂ := eq27
       grind)
    | exact resolve eq206304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206304
  have eq206408 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq206359
       grind)
    | exact superpose eq206359 eq18
    | exact resolve eq18 eq206359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq206409 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq206359
       grind)
    | exact superpose eq206359 eq24
    | exact resolve eq24 eq206359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq206359
  have eq213769 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq206409
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq206409
    | exact resolve eq206409 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206409
  have eq215283 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq213769 eq26
    | exact resolve eq26 eq213769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq213769
  have eq220114 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq135 x
       have i₂ := eq206408
       grind)
    | exact superpose eq206408 eq135
    | exact resolve eq135 eq206408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq206408
  have eq220277 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq220114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq220114
    | exact resolve eq220114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq220114
  have eq220327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq215283 eq220277
    | exact resolve eq220277 eq215283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215283 eq220277
  have eq220359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq220327
    | exact resolve eq220327 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq220327
  have eq220373 : False := by grind
  exact eq220373

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pxy_pyy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq108 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq109 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq43
    | exact resolve eq43 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq114
    | exact resolve eq114 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq113
    | exact resolve eq113 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq127 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq111 sF3
       grind)
    | exact superpose eq111 eq101
    | exact resolve eq101 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq127
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq127
    | exact resolve eq127 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq111 sF1
       grind)
    | exact superpose eq111 eq138
    | exact resolve eq138 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq111 sF0
       grind)
    | exact superpose eq111 eq141
    | exact resolve eq141 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq166 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : x = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq111 (τ X0)
       grind)
    | exact superpose eq111 eq34
    | exact resolve eq34 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq340 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq329 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq329
    | exact resolve eq329 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq340 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq340
    | exact resolve eq340 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq340
  have eq517 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 (M.op X2 (M.op (M.op x y) (M.op X1 y)))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4) (M.op X3 X4)) = (M.op X0 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4 X3 X2
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 X1) y)) X2) (M.op X1 X2)) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) X2 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 x X2
       have i₂ := eq52 X0 x X2 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) (M.op (σ x) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X3 X2 x
       have i₂ := eq52 X0 x X2 X1
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq55 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X5 (M.op (M.op X0 X4) X2))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X1 (M.op (M.op X2 X3) (M.op X4 X3)) (M.op (M.op X0 X4) X2) X5
       have i₂ := eq55 X2 X0 X4 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq827 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq16
    | exact resolve eq16 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq253 eq537
    | exact resolve eq537 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq1188 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq263 eq537
    | exact resolve eq537 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1198 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq537 (M.op X0 X1) X2 (M.op X1 X2)
       have i₂ := eq537 X0 X1 X2
       grind)
    | exact superpose eq537 eq537
    | exact resolve eq537 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1199 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq537 (M.op X0 X1) (M.op X2 X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq537
    | exact resolve eq537 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1200 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq537
    | exact resolve eq537 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq537
    | exact resolve eq537 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq54 eq537
    | exact resolve eq537 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1450 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq263 eq639
    | exact resolve eq639 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1454 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq639 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq639
    | (have j0 := eq639 X0 x y
       grind)
    | exact resolve eq639 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1458 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq639
    | (have j0 := eq639 X0 (σ x) (σ y)
       grind)
    | exact resolve eq639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1462 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq639 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq541 X0 X2 X2
       grind)
    | exact superpose eq541 eq639
    | exact resolve eq639 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1466 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq639 (M.op (M.op X0 (M.op X1 X2)) X2) X1 X2
       have i₂ := eq537 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq537 eq639
    | exact resolve eq639 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1511 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op x sF3)
       have i₂ := eq639 sF4 x sF3
       grind)
    | exact superpose eq639 eq51
    | exact resolve eq51 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2062 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) y) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1454 (M.op (M.op X0 sF0) y)
       have i₂ := eq537 X0 sF0 y
       grind)
    | exact superpose eq537 eq1454
    | exact resolve eq1454 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2104 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq1454 eq50
    | exact resolve eq50 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1454
  have eq2424 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1458 (M.op (M.op X0 sF4) sF3)
       have i₂ := eq537 X0 sF4 sF3
       grind)
    | exact superpose eq537 eq1458
    | exact resolve eq1458 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2475 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1458 eq51
    | exact resolve eq51 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1458
  have eq2503 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2475 eq537
    | exact resolve eq537 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2520 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2475 eq639
    | exact resolve eq639 eq2475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475
  have eq2521 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1211 eq2520
    | exact resolve eq2520 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211 eq2520
  have eq2737 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1511 eq541
    | exact resolve eq541 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3020 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op X1 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 x
       have i₂ := eq52 X0 x y X1
       grind)
    | exact superpose eq52 eq272
    | exact resolve eq272 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3473 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | exact superpose eq2062 eq537
    | exact resolve eq537 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq3822 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq2424 eq537
    | exact resolve eq537 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq4958 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq2521 eq1511
    | exact resolve eq1511 eq2521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521
  have eq4963 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2737 eq4958
    | exact resolve eq4958 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4958
  have eq6681 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4963 eq541
    | exact resolve eq541 eq4963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963
  have eq12035 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1200 (M.op (M.op y (M.op X0 X0)) X0)
       have i₂ := eq635 y X0 X0 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq635 eq1200
    | exact resolve eq1200 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq12036 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1201 (M.op (M.op sF3 (M.op x x)) x)
       have i₂ := eq635 sF3 x x (M.op sF3 (M.op x x))
       grind)
    | exact superpose eq635 eq1201
    | exact resolve eq1201 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq1201
  have eq12293 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12035 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq12035
    | exact resolve eq12035 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12295 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12035 (τ X0)
       have i₂ := eq827 X0
       grind)
    | exact superpose eq827 eq12035
    | exact resolve eq12035 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12035
  have eq12385 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12036 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq12036
    | exact resolve eq12036 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq12396 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq12036 eq541
    | exact resolve eq541 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12036
  have eq12594 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12396 (τ X0)
       have i₂ := eq827 X0
       grind)
    | exact superpose eq827 eq12396
    | exact resolve eq12396 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq12613 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq12396 eq541
    | exact resolve eq541 eq12396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq12396
  have eq19125 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 y) y)) (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq534 eq272
    | exact resolve eq272 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq534
  have eq19230 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq19125 x
       have i₂ := eq639 sF0 x y
       grind)
    | exact superpose eq639 eq19125
    | exact resolve eq19125 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq19125
  have eq22826 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1462 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X2
       have i₂ := eq537 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq537 eq1462
    | exact resolve eq1462 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq24125 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1466 (M.op (M.op X0 X2) X1) X2 X1
       have i₂ := eq537 X0 X2 X1
       grind)
    | exact superpose eq537 eq1466
    | exact resolve eq1466 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq1466
  have eq31996 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op X1 (σ x)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq613
    | (have j0 := eq613 X0 X1 (σ x)
       grind)
    | exact resolve eq613 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq32479 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31996 X0 X1
       have i₂ := eq1198 (M.op (M.op X0 X1) (M.op sF4 sF4)) X1 sF2
       grind)
    | exact superpose eq1198 eq31996
    | exact resolve eq31996 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31996
  have eq32555 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1450 eq32479
    | exact resolve eq32479 eq1450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450 eq32479
  have eq58275 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq596 X2 (M.op X0 X1) X1 x x
       have i₂ := eq533 X1 x X0 X1 x
       grind)
    | exact superpose eq533 eq596
    | exact resolve eq596 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq131253 : ∀ X0 X2 X3 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op X2 y) (M.op x y)))) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq538 eq647
    | exact resolve eq647 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq647
  have eq134720 : ∀ X0 X2 X3 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op x y) (M.op X2 y)))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq131253 X0 X2 X2
       have i₂ := eq58275 (M.op X2 y) sF0 X2
       grind)
    | (have i₁ := eq131253 X0 X2 X2
       have i₂ := eq58275 sF0 (M.op X2 y) X2
       grind)
    | exact superpose eq58275 eq131253
    | exact resolve eq131253 eq58275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58275 eq131253
  have eq135666 : ∀ X0 X2 : G, (M.op (M.op X0 X2) x) = (M.op (M.op X0 x) X2) := by
    intro X0 X2
    first
    | exact superpose eq517 eq134720
    | exact resolve eq134720 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq134720
  have eq203094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq203094
    | exact resolve eq203094 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203094
  have eq203118 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq203111
       have r₂ := eq27
       grind)
    | exact resolve eq203111 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203111
  have eq203120 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq203118
    | exact resolve eq203118 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203118
  have eq203122 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq203120
    | exact resolve eq203120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203120
  have eq203124 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq203122 eq109
    | (have r₁ := eq109
       have r₂ := eq203122
       grind)
    | exact resolve eq109 eq203122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq203122
  have eq203378 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq203124
  have eq203379 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq203378
  have eq203642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq203379 eq96
    | exact resolve eq96 eq203379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq203379
  have eq203658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq203642
  have eq203666 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq203658
       have r₂ := eq27
       grind)
    | exact resolve eq203658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203658
  have eq203671 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq203666
       grind)
    | exact superpose eq203666 eq108
    | (have r₁ := eq108
       have r₂ := eq203666
       grind)
    | exact resolve eq108 eq203666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq203672 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq203666
       grind)
    | exact superpose eq203666 eq119
    | exact resolve eq119 eq203666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq203666
  have eq203930 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq203671
  have eq203931 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq203930
  have eq204106 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq203672
    | exact resolve eq203672 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203672
  have eq204204 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq203931
       grind)
    | exact superpose eq203931 eq74
    | exact resolve eq74 eq203931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq203931
  have eq204240 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq204204
    | exact resolve eq204204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204204
  have eq204896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq204240 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq204240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204240
  have eq204915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq204896
    | exact resolve eq204896 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204896
  have eq204922 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq204915
       have r₂ := eq27
       grind)
    | exact resolve eq204915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204915
  have eq204924 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq204922
    | exact resolve eq204922 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204922
  have eq204926 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq204924
    | exact resolve eq204924 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204924
  have eq204927 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq204926
  have eq204947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204927 eq204106
    | exact resolve eq204106 eq204927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204106 eq204927
  have eq205186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq204947
  have eq205351 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq205186
       have r₂ := eq27
       grind)
    | exact resolve eq205186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205186
  have eq205630 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq205351 eq1511
    | exact resolve eq1511 eq205351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq205635 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq205351 eq2503
    | exact resolve eq2503 eq205351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq205651 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq205351 eq6681
    | exact resolve eq6681 eq205351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6681 eq205351
  have eq205696 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2737 eq205651
    | exact resolve eq205651 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737 eq205651
  have eq205710 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq205635
    | exact resolve eq205635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq205635
  have eq205935 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq205710 eq1188
    | exact resolve eq1188 eq205710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205710
  have eq207421 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (M.op (σ y) (σ y)) (M.op (M.op X0 X1) (σ y))) X2) (M.op X1 X2)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq205696 eq533
    | exact resolve eq533 eq205696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205696
  have eq207681 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq207421 x x x
       have i₂ := eq533 sF3 sF3 x x x
       grind)
    | exact superpose eq533 eq207421
    | exact resolve eq207421 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq207421
  have eq219221 : (M.op x y) = (M.op x (M.op y (τ (σ x)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq205630 eq12295
    | exact resolve eq12295 eq205630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12295
  have eq219229 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (τ (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq205630 eq12594
    | exact resolve eq12594 eq205630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12594 eq205630
  have eq219591 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq219229
    | exact resolve eq219229 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219229
  have eq219595 : (M.op x y) = (M.op x (M.op y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq219221
    | exact resolve eq219221 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq219221
  have eq219873 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq219591
       have i₂ := eq135666 sF4 sF3
       grind)
    | exact superpose eq135666 eq219591
    | exact resolve eq219591 eq135666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219591
  have eq219876 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq219595
       have i₂ := eq3473 x
       grind)
    | exact superpose eq3473 eq219595
    | exact resolve eq219595 eq3473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3473 eq219595
  have eq220741 : (σ x) = (M.op (M.op (σ y) x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq207681 eq219873
    | exact resolve eq219873 eq207681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207681 eq219873
  have eq220972 : (σ x) = (M.op (M.op (σ y) x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq220741
  have eq232390 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq220972 eq1199
    | exact resolve eq1199 eq220972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220972
  have eq238582 : (M.op x x) = (τ (M.op (σ x) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq232390 eq117
    | exact resolve eq117 eq232390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232390
  have eq262835 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) x) (M.op (σ x) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq238582 eq342
    | exact resolve eq342 eq238582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238582
  have eq262877 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1188 eq262835
    | exact resolve eq262835 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262835
  have eq262885 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq262877
       have i₂ := eq1181 x
       grind)
    | exact superpose eq1181 eq262877
    | exact resolve eq262877 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262877
  have eq262886 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq144 eq262885
    | exact resolve eq262885 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262885
  have eq262903 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq262886 eq205935
    | exact resolve eq205935 eq262886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205935 eq262886
  have eq263151 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq262903
  have eq265246 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263151 eq128
    | exact resolve eq128 eq263151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq263151
  have eq265679 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq166 eq265246
    | exact resolve eq265246 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq265246
  have eq270789 : (M.op x (M.op x y)) = (M.op (M.op (M.op y y) (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq265679 eq19230
    | exact resolve eq19230 eq265679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19230 eq265679
  have eq271191 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53 eq270789
    | exact resolve eq270789 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq270789
  have eq271421 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq271191 eq219876
    | exact resolve eq219876 eq271191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219876 eq271191
  have eq271633 : y = (M.op x y) := by grind
  clear eq271421
  have eq271910 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq271633 eq20
    | exact resolve eq20 eq271633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq272019 : x = (M.op (M.op y x) y) := by
    first
    | exact superpose eq271633 eq2104
    | exact resolve eq2104 eq271633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104
  have eq272184 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq271910
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq271910
    | exact resolve eq271910 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq271910
  have eq291076 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq3020 X0 X1
       have i₂ := eq24125 X0 (M.op X1 y) X1
       grind)
    | (have i₁ := eq3020 X0 X1
       have i₂ := eq24125 X0 X1 (M.op X1 y)
       grind)
    | exact superpose eq24125 eq3020
    | exact resolve eq3020 eq24125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020 eq24125
  have eq291077 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq291076 X0 X1
       have i₂ := eq135666 X0 sF0
       grind)
    | exact superpose eq135666 eq291076
    | exact resolve eq291076 eq135666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135666 eq291076
  have eq291078 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq271633 eq291077
    | exact resolve eq291077 eq271633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291077
  have eq291793 : (M.op x y) = (M.op x (M.op y (σ (M.op (M.op y x) y)))) := by
    first
    | (have i₁ := eq12293 (M.op y y)
       have i₂ := eq291078 y y
       grind)
    | exact superpose eq291078 eq12293
    | exact resolve eq12293 eq291078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12293
  have eq291796 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op (M.op y x) y)))) := by
    first
    | (have i₁ := eq12385 (M.op y y)
       have i₂ := eq291078 y y
       grind)
    | exact superpose eq291078 eq12385
    | exact resolve eq12385 eq291078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12385 eq291078
  have eq292209 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq291796
       have i₂ := eq272019
       grind)
    | exact superpose eq272019 eq291796
    | exact resolve eq291796 eq272019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291796
  have eq292212 : (M.op x y) = (M.op x (M.op y (σ x))) := by
    first
    | (have i₁ := eq291793
       have i₂ := eq272019
       grind)
    | exact superpose eq272019 eq291793
    | exact resolve eq291793 eq272019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272019 eq291793
  have eq292903 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq292209
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq292209
    | exact resolve eq292209 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292209
  have eq292906 : (M.op x y) = (M.op x (M.op y (σ x))) := by
    first
    | (have i₁ := eq292212
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq292212
    | exact resolve eq292212 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq292212
  have eq293419 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3822 eq292903
    | exact resolve eq292903 eq3822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3822 eq292903
  have eq293421 : y = (M.op x (M.op y (σ x))) := by
    first
    | exact superpose eq271633 eq292906
    | exact resolve eq292906 eq271633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271633 eq292906
  have eq294233 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq293419 eq12613
    | exact resolve eq12613 eq293419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12613 eq293419
  have eq294599 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq272184 eq294233
    | exact resolve eq294233 eq272184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272184 eq294233
  have eq295040 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y (σ x)) y)) := by
    intro X0
    first
    | exact superpose eq293421 eq1198
    | exact resolve eq1198 eq293421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq293421
  have eq295081 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq295040 X0
       have i₂ := eq1199 X0 sF2 y
       grind)
    | exact superpose eq1199 eq295040
    | exact resolve eq295040 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq295040
  have eq302783 : (M.op x x) = (τ (M.op (σ x) x)) := by
    first
    | exact superpose eq295081 eq117
    | exact resolve eq117 eq295081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq295081
  have eq320165 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) x) (M.op (σ x) x)) := by
    first
    | exact superpose eq302783 eq342
    | exact resolve eq342 eq302783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq302783
  have eq320231 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq1188 eq320165
    | exact resolve eq320165 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188 eq320165
  have eq320252 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq320231
       have i₂ := eq1181 x
       grind)
    | exact superpose eq1181 eq320231
    | exact resolve eq320231 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq320231
  have eq320261 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq294599 eq320252
    | exact resolve eq320252 eq294599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294599 eq320252
  have eq320270 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq144 eq320261
    | exact resolve eq320261 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq320261
  have eq320489 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ x))) (σ (M.op x y))) := by
    first
    | exact superpose eq320270 eq32555
    | exact resolve eq32555 eq320270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32555 eq320270
  have eq320511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq320489
       have i₂ := eq22826 sF1 sF1 sF2
       grind)
    | exact superpose eq22826 eq320489
    | exact resolve eq320489 eq22826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22826 eq320489
  have eq320715 : False := by grind
  exact eq320715

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 X0 y x
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 X0 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq96 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq58 eq57
    | exact resolve eq57 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq61 eq117
    | exact resolve eq117 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq125 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq140 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq181 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140
    | exact resolve eq140 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq322 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (M.op (σ x) (σ y)) (σ (k y x))
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq326 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq322
    | exact resolve eq322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq328 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq326
    | exact resolve eq326 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq376 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq54 X0 x X2 X1
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x
       have i₂ := eq54 sF0 x y x
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq58 x
       have i₂ := eq54 sF4 x sF3 x
       grind)
    | exact superpose eq54 eq58
    | exact resolve eq58 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq54 (M.op X0 X1) X2 X1 x
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq376 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq376
    | (have j0 := eq376 X0 x y
       grind)
    | exact resolve eq376 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq376
    | (have j0 := eq376 X0 (σ x) (σ y)
       grind)
    | exact resolve eq376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq376 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) X2 X3
       have i₂ := eq376 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq376 eq376
    | exact resolve eq376 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (σ y))) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq58 eq376
    | exact resolve eq376 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2
       have i₂ := eq376 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq376 eq9
    | exact resolve eq9 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op X0 (M.op y sF0))
       have i₂ := eq376 X0 y sF0
       grind)
    | exact superpose eq376 eq55
    | exact resolve eq55 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op X0 (M.op sF3 sF4))
       have i₂ := eq376 X0 sF3 sF4
       grind)
    | exact superpose eq376 eq57
    | exact resolve eq57 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op X1 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq376 X0 X1 y
       grind)
    | exact superpose eq376 eq55
    | exact resolve eq55 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq473 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op X1 y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq376 X0 X1 y
       grind)
    | exact superpose eq376 eq53
    | exact resolve eq53 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq474 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op X1 (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq376 X0 X1 sF3
       grind)
    | exact superpose eq376 eq58
    | exact resolve eq58 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq475 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (M.op X1 (σ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq376 X0 X1 sF3
       grind)
    | exact superpose eq376 eq57
    | exact resolve eq57 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq475 eq474
    | (have j0 := eq474 X0 (σ x)
       grind)
    | exact resolve eq474 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq479 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq473 X0 x
       have i₂ := eq472 X0 x
       grind)
    | (have i₁ := eq473 X0 x
       have i₂ := eq472 X0 x
       grind)
    | exact superpose eq472 eq473
    | (have j0 := eq473 X0 x
       grind)
    | exact resolve eq473 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq473
  have eq539 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq464 eq376
    | exact resolve eq376 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq574 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq465 eq376
    | exact resolve eq376 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq725 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq382 (M.op X0 (M.op X3 X2)) X3 X4
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq382
    | exact resolve eq382 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq108 eq382
    | exact resolve eq382 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq810 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X4 X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3 X4
       have i₂ := eq382 X0 X1 X2
       grind)
    | exact superpose eq382 eq54
    | exact resolve eq54 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X2 (M.op X0 (M.op X1 X2)) X1 X3
       have i₂ := eq376 X0 X1 X2
       grind)
    | exact superpose eq376 eq56
    | exact resolve eq56 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) X0) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq102 eq56
    | exact resolve eq56 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1019 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq56 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq376 (M.op (M.op X0 X1) X2) (M.op X2 X3) (M.op X1 X3)
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq376
    | exact resolve eq376 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X5 X4)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) X2) (M.op (M.op X2 X3) (M.op X1 X3)) X4 X5
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1033 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1026 X0 X1 X2 X3 X4 x
       have i₂ := eq810 X0 X1 X2 X4 x
       grind)
    | exact superpose eq810 eq1026
    | exact resolve eq1026 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq1026
  have eq1068 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq739 eq935
    | exact resolve eq935 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq935
  have eq1075 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq923 X0 X1 X2 x x
       have i₂ := eq725 X2 x X1 X2 x
       grind)
    | exact superpose eq725 eq923
    | exact resolve eq923 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq923
  have eq1133 : ∀ X0 : G, (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0 (τ X0)
       have i₂ := eq125 (τ X0)
       grind)
    | exact superpose eq125 eq50
    | (have j1 := eq125 (τ X0)
       grind)
    | exact resolve eq50 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq125
  have eq1144 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1133 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1133
    | (have j0 := eq1133 X0
       grind)
    | exact resolve eq1133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1146 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1144 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1144
    | (have j0 := eq1144 X0
       grind)
    | exact resolve eq1144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1148 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1146 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1146 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq1146 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1181 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0 X0
       have i₂ := eq1148 X0
       grind)
    | exact superpose eq1148 eq181
    | exact resolve eq181 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1182 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1148 (σ X0)
       grind)
    | exact superpose eq1148 eq15
    | exact resolve eq15 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1182 X0
       have i₂ := eq1148 X0
       grind)
    | exact superpose eq1148 eq1182
    | exact resolve eq1182 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1184 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1181 X0
       have i₂ := eq1148 (τ X0)
       grind)
    | exact superpose eq1148 eq1181
    | exact resolve eq1181 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq1181
  have eq1195 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1068 eq376
    | exact resolve eq376 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1219 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1195 eq442
    | exact resolve eq442 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq1262 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq1219 eq9
    | exact resolve eq9 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1268 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (σ x))) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1219 eq376
    | exact resolve eq376 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1272 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1268 X0
       have i₂ := eq1021 X0 sF2 sF4 sF2
       grind)
    | exact superpose eq1021 eq1268
    | exact resolve eq1268 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1277 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1262 X0
       have i₂ := eq1021 (M.op X0 sF3) sF2 sF4 sF2
       grind)
    | exact superpose eq1021 eq1262
    | exact resolve eq1262 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq1262
  have eq1322 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1272 (M.op X0 (M.op sF2 sF4))
       have i₂ := eq376 X0 sF2 sF4
       grind)
    | exact superpose eq376 eq1272
    | exact resolve eq1272 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1272 eq57
    | exact resolve eq57 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1272
  have eq1340 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1325 eq475
    | exact resolve eq475 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq1341 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1325 eq477
    | exact resolve eq477 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq1325
  have eq1378 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1277 (M.op X0 (M.op sF3 sF2))
       have i₂ := eq376 X0 sF3 sF2
       grind)
    | exact superpose eq376 eq1277
    | exact resolve eq1277 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1569 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (M.op (σ y) (σ x)) X1)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1378 eq54
    | exact resolve eq54 eq1378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1669 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op x (M.op y X1))) := by
    intro X0 X1
    first
    | exact superpose eq380 eq1019
    | exact resolve eq1019 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1670 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq381 eq1019
    | exact resolve eq1019 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1673 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1019 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq382 X0 X2 X3
       grind)
    | exact superpose eq382 eq1019
    | exact resolve eq1019 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1675 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X3 X2))) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1019 X1 (M.op (M.op X0 X2) (M.op X3 X2)) X3
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq1019
    | exact resolve eq1019 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1679 : ∀ X0 X1 : G, (M.op X1 (M.op X0 y)) = (M.op X1 (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0 X1
    first
    | exact superpose eq421 eq1019
    | exact resolve eq1019 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq1695 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1019 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq376 X0 X2 X2
       grind)
    | exact superpose eq376 eq1019
    | exact resolve eq1019 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1725 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op X2 X1)
       have i₂ := eq1019 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq1019 eq9
    | exact resolve eq9 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1813 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1679 eq479
    | exact resolve eq479 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq1679
  have eq1827 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq921 X0 X1 X2 x
       have i₂ := eq1675 X2 X0 x X1
       grind)
    | exact superpose eq1675 eq921
    | exact resolve eq921 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq1832 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1033 X0 X1 X2 x X4
       have i₂ := eq1675 X2 X4 x X1
       grind)
    | exact superpose eq1675 eq1033
    | exact resolve eq1033 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq1675
  have eq1890 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) X1))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1569 X1 x X2
       have i₂ := eq1673 sF3 X1 sF2 x
       grind)
    | exact superpose eq1673 eq1569
    | exact resolve eq1569 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1947 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1341 X0
       have i₂ := eq1673 X0 (M.op sF4 X0) sF2 sF4
       grind)
    | exact superpose eq1673 eq1341
    | exact resolve eq1341 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1953 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 x
       have i₂ := eq1673 X0 sF4 x sF3
       grind)
    | exact superpose eq1673 eq449
    | exact resolve eq449 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq2077 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1322 eq1947
    | exact resolve eq1947 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq2407 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) X1))) X2) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2077 eq54
    | exact resolve eq54 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2416 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2407 X0 x X1
       have i₂ := eq446 X0 X1 sF4 x
       grind)
    | exact superpose eq446 eq2407
    | exact resolve eq2407 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407
  have eq2641 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq381 (M.op sF3 x)
       have i₂ := eq1075 (M.op sF4 (M.op sF3 x)) x sF3
       grind)
    | exact superpose eq1075 eq381
    | exact resolve eq381 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq2852 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2641 eq376
    | exact resolve eq376 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2873 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2852 eq1953
    | exact resolve eq1953 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq3098 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq463 X3 X4 (M.op X0 (M.op X4 X2))
       have i₂ := eq54 X0 X1 X2 X4
       grind)
    | exact superpose eq54 eq463
    | exact resolve eq463 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3102 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) y)) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq539 eq463
    | exact resolve eq463 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq3199 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) y)) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | exact superpose eq1669 eq3102
    | exact resolve eq3102 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq3102
  have eq3203 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3098 X0 X1 X2 X3 X4
       have i₂ := eq1673 X0 X4 X1 (M.op X2 X1)
       grind)
    | exact superpose eq1673 eq3098
    | exact resolve eq3098 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098
  have eq3229 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3199 X0 X1
       have i₂ := eq1673 X0 X1 x y
       grind)
    | exact superpose eq1673 eq3199
    | exact resolve eq3199 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3199
  have eq3232 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3203 X0 x X2 X3 X4
       have i₂ := eq463 X0 x X2
       grind)
    | exact superpose eq463 eq3203
    | exact resolve eq3203 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq3203
  have eq3251 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3229 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3229
    | (have j0 := eq3229 X0 X1
       grind)
    | exact resolve eq3229 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3255 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (M.op (σ y) X1))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1890 x X2 X2
       have i₂ := eq3232 sF3 X2 x sF2
       grind)
    | (have i₁ := eq1890 x X2 X2
       have i₂ := eq3232 sF2 X2 x sF3
       grind)
    | exact superpose eq3232 eq1890
    | exact resolve eq1890 eq3232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1890 eq3232
  have eq3323 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 X0 X1 (M.op X2 X2)
       have i₂ := eq1695 X1 X0 X2
       grind)
    | exact superpose eq1695 eq376
    | exact resolve eq376 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3324 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X0 X2 (M.op X3 X3) X1
       have i₂ := eq1695 X1 X0 X3
       grind)
    | exact superpose eq1695 eq54
    | exact resolve eq54 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3385 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3324 X0 X1 X2 X3
       have i₂ := eq1673 X3 (M.op X0 X2) X3 X2
       grind)
    | exact superpose eq1673 eq3324
    | exact resolve eq3324 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3416 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3385 X0 X1 X2 x
       have i₂ := eq1075 (M.op X0 X2) X2 x
       grind)
    | exact superpose eq1075 eq3385
    | exact resolve eq3385 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq3598 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (σ x)))) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2641 eq96
    | exact resolve eq96 eq2641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2641
  have eq3673 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3598 x
       have i₂ := eq446 sF4 sF3 x sF2
       grind)
    | exact superpose eq446 eq3598
    | exact resolve eq3598 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq3598
  have eq4352 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq376 (M.op (M.op X0 X2) X1) X1 X2
       have i₂ := eq1725 X0 X2 X1
       grind)
    | exact superpose eq1725 eq376
    | exact resolve eq376 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq4412 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1340 X0 x
       have i₂ := eq4352 X0 (M.op x sF3) x
       grind)
    | (have i₁ := eq1340 X0 X1
       have i₂ := eq4352 X0 X1 (M.op X1 sF3)
       grind)
    | exact superpose eq4352 eq1340
    | exact resolve eq1340 eq4352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq4459 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2416 X0 X1
       have i₂ := eq4352 X0 (M.op X1 sF3) sF2
       grind)
    | (have i₁ := eq2416 X0 X1
       have i₂ := eq4352 X0 sF2 (M.op X1 sF3)
       grind)
    | exact superpose eq4352 eq2416
    | exact resolve eq2416 eq4352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq4466 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3255 X0 X1 X2
       have i₂ := eq4352 X0 (M.op sF2 (M.op sF3 X1)) sF4
       grind)
    | (have i₁ := eq3255 X0 X1 X2
       have i₂ := eq4352 X0 sF4 (M.op sF2 (M.op sF3 X1))
       grind)
    | exact superpose eq4352 eq3255
    | exact resolve eq3255 eq4352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3255 eq4352
  have eq5687 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq574 eq3323
    | exact resolve eq3323 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6825 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X1)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3416 (M.op (M.op X0 X1) X2) X3 (M.op X2 X1)
       have i₂ := eq1725 X0 X1 X2
       grind)
    | exact superpose eq1725 eq3416
    | exact resolve eq3416 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq7275 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq3673 eq3416
    | exact resolve eq3416 eq3673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416 eq3673
  have eq7276 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq7275 x x
       have i₂ := eq6825 sF4 x sF2 x
       grind)
    | exact superpose eq6825 eq7275
    | exact resolve eq7275 eq6825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825 eq7275
  have eq7301 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq2852 eq7276
    | exact resolve eq7276 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7276
  have eq10488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq328
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq328
    | (have j1 := eq14 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq328 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq10502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10488
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10488
    | exact resolve eq10488 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10488
  have eq10505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq10502
    | exact resolve eq10502 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502
  have eq10506 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10505
       have r₂ := eq28
       grind)
    | exact resolve eq10505 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10505
  have eq10507 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10506
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10506
    | exact resolve eq10506 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10506
  have eq10509 : (σ y) ≠ (σ y) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10507 eq120
    | (have r₁ := eq120
       have r₂ := eq10507
       grind)
    | exact resolve eq120 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq10512 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10507 eq1195
    | exact resolve eq1195 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10513 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10507 eq1322
    | exact resolve eq1322 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10507
  have eq10528 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10509
  have eq10532 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq10513
    | (have j0 := eq10513 X0
       grind)
    | exact resolve eq10513 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513
  have eq11273 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10528
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq10528
    | (have j1 := eq14 (σ (M.op x y)) (M.op (σ y) (σ x))
       grind)
    | exact resolve eq10528 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10528
  have eq11289 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq11273
  have eq11292 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11289
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11289
    | exact resolve eq11289 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11289
  have eq11295 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq11292
    | exact resolve eq11292 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11292
  have eq11298 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11295
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11295
    | exact resolve eq11295 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11295
  have eq11299 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11298
  have eq11312 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11299 eq10512
    | exact resolve eq10512 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10512
  have eq11324 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11299 eq1827
    | exact resolve eq1827 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827 eq11299
  have eq11333 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11312
  have eq11336 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq11324
    | (have j0 := eq11324 X0
       grind)
    | exact resolve eq11324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324
  have eq11362 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11333 eq3323
    | exact resolve eq3323 eq11333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11333
  have eq11371 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (M.op X0 X0)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2852 eq11362
    | exact resolve eq11362 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11362
  have eq11380 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11371 X0
       have i₂ := eq1075 sF4 (M.op X0 X0) sF3
       grind)
    | exact superpose eq1075 eq11371
    | exact resolve eq11371 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11371
  have eq12002 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10532 eq11380
    | exact resolve eq11380 eq10532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10532 eq11380
  have eq12043 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12002
  have eq12063 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1670 eq12043
    | exact resolve eq12043 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670 eq12043
  have eq12085 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12063
       have i₂ := eq1695 sF2 sF4 sF3
       grind)
    | exact superpose eq1695 eq12063
    | exact resolve eq12063 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12063
  have eq12258 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12085 eq1195
    | exact resolve eq1195 eq12085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq12308 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12258 eq11336
    | exact resolve eq11336 eq12258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11336 eq12258
  have eq12326 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12308
  have eq12358 : (τ (σ x)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12326 eq1184
    | exact resolve eq1184 eq12326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq12326
  have eq12393 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq38 eq12358
    | exact resolve eq12358 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq12358
  have eq12399 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq39 eq12393
    | exact resolve eq12393 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393
  have eq12411 : x = (M.op x (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12399 eq380
    | exact resolve eq380 eq12399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq12399
  have eq12455 : x = (M.op x (M.op x (M.op y y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3251 eq12411
    | exact resolve eq12411 eq3251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251 eq12411
  have eq12472 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12455
       have i₂ := eq1695 x x y
       grind)
    | exact superpose eq1695 eq12455
    | exact resolve eq12455 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12455
  have eq12541 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1183 x
       have i₂ := eq12472
       grind)
    | exact superpose eq12472 eq1183
    | exact resolve eq1183 eq12472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12472
  have eq12582 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12541
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12541
    | exact resolve eq12541 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12541
  have eq12677 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12582 eq574
    | exact resolve eq574 eq12582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq12582
  have eq12717 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2852 eq12677
    | exact resolve eq12677 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12677
  have eq12726 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7301 eq12717
    | exact resolve eq12717 eq7301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7301 eq12717
  have eq12731 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12726
    | exact resolve eq12726 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12726
  have eq12769 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12731 eq3323
    | exact resolve eq3323 eq12731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323 eq12731
  have eq12782 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5687 eq12769
    | exact resolve eq12769 eq5687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5687 eq12769
  have eq12798 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2852 eq12782
    | exact resolve eq12782 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852 eq12782
  have eq12810 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2873 eq12798
    | exact resolve eq12798 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873 eq12798
  have eq12819 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12810
       have i₂ := eq1695 sF2 sF4 sF3
       grind)
    | exact superpose eq1695 eq12810
    | exact resolve eq12810 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695 eq12810
  have eq13019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12819 eq12085
    | exact resolve eq12085 eq12819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12085 eq12819
  have eq13048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13019
  have eq13055 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13048
       have r₂ := eq28
       grind)
    | exact resolve eq13048 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13048
  have eq13248 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13055 eq40
    | exact resolve eq40 eq13055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13055
  have eq13265 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq13248
    | exact resolve eq13248 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq13248
  have eq13266 : y = (M.op x y) ∨ x = y := by grind
  clear eq13265
  have eq13270 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13266 eq21
    | exact resolve eq21 eq13266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13279 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op X0 y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13266 eq1813
    | exact resolve eq1813 eq13266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq13266
  have eq13294 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13270
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13270
    | exact resolve eq13270 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13270
  have eq16066 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ x = y := by
    first
    | (have i₁ := eq1183 (M.op y y)
       have i₂ := eq13279 y
       grind)
    | exact superpose eq13279 eq1183
    | exact resolve eq1183 eq13279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13279
  have eq16120 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq16066
       have i₂ := eq1183 y
       grind)
    | exact superpose eq1183 eq16066
    | exact resolve eq16066 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16066
  have eq16164 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ y) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq16120
       have i₂ := eq4466 (σ y) (σ y) (σ y)
       grind)
    | exact superpose eq4466 eq16120
    | exact resolve eq16120 eq4466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466 eq16120
  have eq16194 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (M.op (σ y) (σ y))) (σ y))) ∨ x = y := by
    first
    | exact superpose eq4459 eq16164
    | exact resolve eq16164 eq4459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459 eq16164
  have eq16213 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ x = y := by
    first
    | (have i₁ := eq16194
       have i₂ := eq1673 sF2 (M.op (σ y) sF2) (M.op sF3 (σ y)) sF3
       grind)
    | exact superpose eq1673 eq16194
    | exact resolve eq16194 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673 eq16194
  have eq16221 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y))))) ∨ x = y := by
    first
    | (have i₁ := eq16213
       have i₂ := eq1832 (M.op (σ y) sF2) (M.op sF3 (σ y)) sF3 sF2
       grind)
    | (have i₁ := eq16213
       have i₂ := eq1832 (M.op (σ y) sF2) sF3 (M.op sF3 (σ y)) sF2
       grind)
    | exact superpose eq1832 eq16213
    | exact resolve eq16213 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832 eq16213
  have eq16227 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq16221
       have i₂ := eq1075 sF2 (σ y) sF3
       grind)
    | exact superpose eq1075 eq16221
    | exact resolve eq16221 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq16221
  have eq16230 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq16227
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16227
    | exact resolve eq16227 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16227
  have eq16233 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq4412 eq16230
    | exact resolve eq16230 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4412 eq16230
  have eq16235 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq16233
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16233
    | exact resolve eq16233 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16233
  have eq16243 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | exact superpose eq16235 eq382
    | exact resolve eq382 eq16235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq16235
  have eq16284 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1322 eq16243
    | exact resolve eq16243 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq16243
  have eq16299 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq16284
    | exact resolve eq16284 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16284
  have eq16325 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq16299 eq28
    | exact resolve eq28 eq16299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299
  have eq16386 : x = y := by
    first
    | (have r₁ := eq16325
       have r₂ := eq13294
       grind)
    | exact resolve eq16325 eq13294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13294 eq16325
  have eq16387 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16386
       grind)
    | exact superpose eq16386 eq19
    | exact resolve eq19 eq16386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq16388 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq16386
       grind)
    | exact superpose eq16386 eq25
    | exact resolve eq25 eq16386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16386
  have eq17052 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16388
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16388
    | exact resolve eq16388 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16388
  have eq17114 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17052 eq27
    | exact resolve eq27 eq17052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17052
  have eq17611 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1183 x
       have i₂ := eq16387
       grind)
    | exact superpose eq16387 eq1183
    | exact resolve eq1183 eq16387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq16387
  have eq17681 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17611
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17611
    | exact resolve eq17611 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17611
  have eq17806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17114 eq17681
    | exact resolve eq17681 eq17114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17114 eq17681
  have eq17916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17806
    | exact resolve eq17806 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17806
  have eq18013 : False := by grind
  exact eq18013

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pyy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X3 X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 X4) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36 X1 X2 X3 (M.op (M.op X0 X4) (M.op X3 X4))
       have i₂ := eq9 X0 X4 X3
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 X3) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36 X0 X1 X2 x
       have i₂ := eq36 X0 X3 X2 x
       grind)
    | exact superpose eq36 eq36
    | exact resolve eq36 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq36 X0 x X2 X1
       grind)
    | exact superpose eq36 eq9
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k X3 (M.op X0 X2)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op X0 X2)
       have i₂ := eq36 X0 X2 X0 X1
       grind)
    | exact superpose eq36 eq12
    | (have j0 := eq12 X3 (M.op X0 X2)
       grind)
    | exact resolve eq12 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq36 (M.op X0 X1) X2 X1 x
       grind)
    | exact superpose eq36 eq9
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X2) (M.op X3 X2))) X3) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq192 X1 (M.op (M.op X0 X2) (M.op X3 X2)) X3
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq192
    | exact resolve eq192 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq192 (M.op X0 (M.op (M.op X1 X2) X1)) X1 X2
       have i₂ := eq192 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq192 eq192
    | exact resolve eq192 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2
       have i₂ := eq192 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq192 eq9
    | exact resolve eq9 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq233 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq243 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq233 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq244 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq246 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq242 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq242 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq242 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq249 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq246 X1
       grind)
    | exact superpose eq246 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq246 X1
       grind)
    | exact superpose eq246 eq244
    | (have j0 := eq244 X0 X1
       grind)
    | exact resolve eq244 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq267 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X2) = (M.op (k X0 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 X0 X0 X1 X2
       have i₂ := eq246 X0
       grind)
    | exact superpose eq246 eq36
    | exact resolve eq36 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X0)) X2) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 X0 X1 X0 X2
       have i₂ := eq246 (M.op X0 X1)
       grind)
    | exact superpose eq246 eq36
    | exact resolve eq36 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq246 (M.op X0 X1)
       grind)
    | exact superpose eq246 eq9
    | exact resolve eq9 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1 x
       have i₂ := eq267 X0 X0 x
       grind)
    | exact superpose eq267 eq272
    | exact resolve eq272 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq288 : ∀ X0 X2 X3 : G, (M.op X0 X2) ≠ (M.op (k X0 X0) (M.op X0 X0)) ∨ (k X3 (M.op X0 X2)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq196 X0 x X2 X3
       have i₂ := eq267 X0 X0 x
       grind)
    | exact superpose eq267 eq196
    | (have j0 := eq196 X0 x X2 X3
       grind)
    | exact resolve eq196 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq267
  have eq298 : ∀ X0 X2 X3 : G, (M.op X0 X2) ≠ (M.op (k X0 X0) (k X0 X0)) ∨ (k X3 (M.op X0 X2)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq288 X0 X2 X3
       have i₂ := eq246 X0
       grind)
    | exact superpose eq246 eq288
    | (have j0 := eq288 X0 X2 X3
       grind)
    | exact resolve eq288 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq300 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq246 X0
       grind)
    | exact superpose eq246 eq286
    | exact resolve eq286 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq307 : ∀ X0 X2 X3 : G, (M.op X0 X2) ≠ (k (k X0 X0) (k X0 X0)) ∨ (k X3 (M.op X0 X2)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq298 X0 X2 X3
       have i₂ := eq246 (k X0 X0)
       grind)
    | exact superpose eq246 eq298
    | (have j0 := eq298 X0 X2 X3
       grind)
    | exact resolve eq298 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq308 : ∀ X0 X2 X3 : G, (M.op X0 X2) ≠ (k (k X0 X0) (k X0 X0)) ∨ (k X3 (k (k X0 X0) (k X0 X0))) = (M.op (k (k X0 X0) (k X0 X0)) X3) := by
    intro X0 X2 X3
    first
    | (have j0 := eq307 X0 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq311 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq246 (k X0 X0)
       grind)
    | exact superpose eq246 eq300
    | exact resolve eq300 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq316 : ∀ X0 : G, (M.op (k (k X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq273 X0 x
       have i₂ := eq311 X0 x
       grind)
    | exact superpose eq311 eq273
    | exact resolve eq273 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq369 : ∀ X0 : G, (τ X0) = (M.op (k (τ (k X0 X0)) (τ (k X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq316 (τ X0)
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq316
    | exact resolve eq316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq379 : ∀ X0 : G, (τ X0) = (M.op (τ (k (k X0 X0) (k X0 X0))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq369 X0
       have i₂ := eq28 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq28 eq369
    | exact resolve eq369 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq389 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X3 (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq209 X3 X0 (M.op X0 X2)
       have i₂ := eq36 X0 X1 X2 X0
       grind)
    | exact superpose eq36 eq209
    | exact resolve eq209 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq419 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X3)) X3) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq201 X0 X1 x X3
       have i₂ := eq389 X0 x X3 (M.op X1 X0)
       grind)
    | exact superpose eq389 eq201
    | exact resolve eq201 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq420 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 X2)) = (M.op (M.op X1 X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184 X0 X1 X2 X3 x
       have i₂ := eq389 X0 x X3 (M.op X1 X0)
       grind)
    | exact superpose eq389 eq184
    | exact resolve eq184 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq421 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 X0 X1 X2 x
       have i₂ := eq389 X0 x X2 (M.op (M.op X1 X2) X0)
       grind)
    | exact superpose eq389 eq37
    | exact resolve eq37 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq457 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq421 X1 X0 X0
       have i₂ := eq246 X0
       grind)
    | exact superpose eq246 eq421
    | exact resolve eq421 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq421 (M.op X1 X2) (M.op X0 X1) X2
       have i₂ := eq197 X0 X1 X2
       grind)
    | exact superpose eq197 eq421
    | exact resolve eq421 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq544 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq214 X3 X4 (M.op X0 (M.op X4 X2))
       have i₂ := eq36 X0 X1 X2 X4
       grind)
    | exact superpose eq36 eq214
    | exact resolve eq214 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq547 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (k X0 X0) X2)) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X1 (M.op X2 X0) (M.op (k X0 X0) X2)
       have i₂ := eq457 X0 X2
       grind)
    | exact superpose eq457 eq214
    | exact resolve eq214 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq601 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq547 X0 X1 X2
       have i₂ := eq461 X1 X2 X0
       grind)
    | exact superpose eq461 eq547
    | exact resolve eq547 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq603 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq544 X0 x X2 X3 X4
       have i₂ := eq389 X0 x X2 X4
       grind)
    | exact superpose eq389 eq544
    | exact resolve eq544 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq544
  have eq800 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X2 X3))) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq214 X1 X3 (M.op (M.op X0 X2) (M.op X2 X3))
       have i₂ := eq419 X2 X0 X3
       grind)
    | exact superpose eq419 eq214
    | exact resolve eq214 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq811 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X0)) = (M.op X1 (M.op X2 (M.op (M.op X0 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq800 X0 X1 X2 X3
       have i₂ := eq603 (M.op X0 X2) X3 X1 X2
       grind)
    | (have i₁ := eq800 X0 X1 X2 X3
       have i₂ := eq603 X2 X3 X1 (M.op X0 X2)
       grind)
    | exact superpose eq603 eq800
    | exact resolve eq800 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq800
  have eq864 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 X3))) = (M.op X1 (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq461 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq197 X0 X2 X3
       grind)
    | exact superpose eq197 eq461
    | exact resolve eq461 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq871 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X1 X3) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq461 X2 X0 (M.op (M.op X1 X3) X3)
       have i₂ := eq461 X0 X1 X3
       grind)
    | exact superpose eq461 eq461
    | exact resolve eq461 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X2 X1 (M.op X0 X1)
       have i₂ := eq461 X1 X0 X1
       grind)
    | exact superpose eq461 eq214
    | exact resolve eq214 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq940 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) (M.op X3 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq871 X0 X1 X2 X3
       have i₂ := eq884 (M.op X1 X3) X3 (M.op X0 X1)
       grind)
    | (have i₁ := eq871 X0 X1 X2 X3
       have i₂ := eq884 X3 (M.op X1 X3) (M.op X0 X1)
       grind)
    | exact superpose eq884 eq871
    | exact resolve eq871 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq884
  have eq947 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X0)) = (M.op X1 (M.op X2 (M.op X0 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq811 X0 X1 X2 X3
       have i₂ := eq864 X0 X2 X2 X3
       grind)
    | exact superpose eq864 eq811
    | exact resolve eq811 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq1021 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (M.op X1 (M.op X3 (M.op X1 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq940 X0 X1 X2 X3
       have i₂ := eq864 X0 X2 X1 (M.op X3 (M.op X1 X3))
       grind)
    | exact superpose eq864 eq940
    | exact resolve eq940 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq940
  have eq1102 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (M.op X3 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1021 X0 x X2 X3
       have i₂ := eq947 X3 X0 x X3
       grind)
    | exact superpose eq947 eq1021
    | exact resolve eq1021 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947 eq1021
  have eq1173 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (k X3 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1102 X0 X2 X3
       have i₂ := eq246 X3
       grind)
    | exact superpose eq246 eq1102
    | exact resolve eq1102 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1404 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (τ (k X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq601 (τ X0) X1 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq601
    | exact resolve eq601 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1415 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X1 X0 (k X2 X2)
       have i₂ := eq601 X2 X0 X0
       grind)
    | exact superpose eq601 eq214
    | exact resolve eq214 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq601
  have eq1425 : ∀ X0 X1 X2 : G, (M.op X1 (k X0 X0)) = (M.op X1 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1415 X0 X1 X2
       have i₂ := eq246 X0
       grind)
    | exact superpose eq246 eq1415
    | exact resolve eq1415 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq1451 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 (σ x) (σ y)
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x (σ y)
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 (τ (k X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1173 X2 X1 (τ X0)
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq1173
    | exact resolve eq1173 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1603 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1425 X2 X1 (τ X0)
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq1425
    | exact resolve eq1425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (τ (τ (k X0 X0))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1404 (τ X0) X1 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq1404
    | exact resolve eq1404 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2012 : ∀ X0 X1 X2 : G, (M.op X0 (τ (k X1 X1))) = (M.op X0 (τ (k X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1404 X2 X0 (τ (k X1 X1))
       have i₂ := eq1548 X1 X0 (τ (k X2 X2))
       grind)
    | exact superpose eq1548 eq1404
    | exact resolve eq1404 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2068 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (M.op X1 (τ (τ (k X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1603 (τ X0) X1 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq1603
    | exact resolve eq1603 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2175 : ∀ X0 X1 X2 : G, (M.op X0 (τ (k X1 X1))) = (M.op X0 (τ (τ (k X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1548 X1 X0 (τ (τ (k X2 X2)))
       have i₂ := eq1645 X2 X0 (τ (k X1 X1))
       grind)
    | exact superpose eq1645 eq1548
    | exact resolve eq1548 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2490 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (M.op X1 (τ (τ (τ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2068 (τ X0) X1 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq2068
    | exact resolve eq2068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2604 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k (k X0 X0) (k X0 X0))) X1) (M.op X2 X1)) = (M.op (τ X0) (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191 (τ (k (k X0 X0) (k X0 X0))) X1 X2 (τ X0)
       have i₂ := eq379 X0
       grind)
    | exact superpose eq379 eq191
    | exact resolve eq191 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq2878 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (k X0 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq420 X0 X0 X1 X2
       have i₂ := eq246 X0
       grind)
    | exact superpose eq246 eq420
    | exact resolve eq420 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq3106 : ∀ X0 X2 : G, (M.op (τ X0) (M.op X2 (τ X0))) = (M.op (k (τ (k (k X0 X0) (k X0 X0))) (τ (k (k X0 X0) (k X0 X0)))) (M.op (τ (k (k X0 X0) (k X0 X0))) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2604 X0 x X2
       have i₂ := eq2878 (τ (k (k X0 X0) (k X0 X0))) x X2
       grind)
    | exact superpose eq2878 eq2604
    | exact resolve eq2604 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2604 eq2878
  have eq3244 : ∀ X0 X2 : G, (M.op (τ X0) (M.op X2 (τ X0))) = (M.op (k (τ (k (k X0 X0) (k X0 X0))) (τ (k (k X0 X0) (k X0 X0)))) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq3106 X0 X2
       have i₂ := eq1404 (k X0 X0) (k (τ (k (k X0 X0) (k X0 X0))) (τ (k (k X0 X0) (k X0 X0)))) X2
       grind)
    | exact superpose eq1404 eq3106
    | exact resolve eq3106 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404 eq3106
  have eq3382 : ∀ X0 X2 : G, (M.op (τ X0) (M.op X2 (τ X0))) = (M.op (τ (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq3244 X0 X2
       have i₂ := eq28 (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))
       grind)
    | exact superpose eq28 eq3244
    | exact resolve eq3244 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244
  have eq5168 : (k (σ y) (σ x)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq1451
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq1451
    | (have j1 := eq256 x (σ y)
       grind)
    | exact resolve eq1451 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq1451
  have eq5169 : y = (k y y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq5168
       have r₂ := eq15 y x
       grind)
    | exact resolve eq5168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5168
  have eq5196 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq15 y y
       have i₂ := eq5169
       grind)
    | exact superpose eq5169 eq15
    | exact resolve eq15 eq5169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5169
  have eq5197 : (σ y) = (k (σ y) (σ y)) := by grind
  clear eq5196
  have eq5211 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1425 X1 X0 (σ y)
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq1425
    | exact resolve eq1425 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq5212 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (τ (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1548 (σ y) X0 X1
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq1548
    | exact resolve eq1548 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq5213 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op X0 (τ (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1603 (σ y) X0 X1
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq1603
    | exact resolve eq1603 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq5215 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (τ (τ (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1645 (σ y) X0 X1
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq1645
    | exact resolve eq1645 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq5218 : ∀ X0 X1 : G, (M.op X0 (τ (k X1 X1))) = (M.op X0 (τ (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2012 X0 X1 (σ y)
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq2012
    | exact resolve eq2012 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012
  have eq5222 : ∀ X0 X1 : G, (M.op X0 (τ (τ (k X1 X1)))) = (M.op X0 (τ (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2175 X0 (σ y) X1
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq2175
    | exact resolve eq2175 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5223 : ∀ X0 X1 : G, (M.op X0 (τ (k X1 X1))) = (M.op X0 (τ (τ (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2175 X0 X1 (σ y)
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq2175
    | exact resolve eq2175 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq5225 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op X0 (τ (τ (τ (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2490 (σ y) X0 X1
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq2490
    | exact resolve eq2490 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2490
  have eq5227 : (τ (σ y)) = (k y (τ (σ y))) := by
    first
    | (have i₁ := eq20 (σ y) y
       have i₂ := eq5197
       grind)
    | exact superpose eq5197 eq20
    | exact resolve eq20 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5197
  have eq5233 : y = (k y y) := by
    first
    | (have i₁ := eq5227
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5227
    | exact resolve eq5227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227
  have eq5234 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op X0 (τ (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq5225 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5225
    | exact resolve eq5225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5225
  have eq5236 : ∀ X0 X1 : G, (M.op X0 (τ (k X1 X1))) = (M.op X0 (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq5223 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5223
    | exact resolve eq5223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5223
  have eq5237 : ∀ X0 X1 : G, (M.op X0 (τ (τ (k X1 X1)))) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq5222 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5222
    | exact resolve eq5222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5222
  have eq5240 : ∀ X0 X1 : G, (M.op X0 (τ (k X1 X1))) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq5218 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5218
    | exact resolve eq5218 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5218
  have eq5243 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (τ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5215 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5215
    | exact resolve eq5215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5215
  have eq5244 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq5213 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5213
    | exact resolve eq5213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5213
  have eq5245 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq5212 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5212
    | exact resolve eq5212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212
  have eq5259 : ∀ X0 X1 : G, (M.op X1 (τ (τ (k X0 X0)))) = (M.op X1 (τ (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2068 X0 X1 x
       have i₂ := eq5234 X1 x
       grind)
    | exact superpose eq5234 eq2068
    | exact resolve eq2068 eq5234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq5269 : ∀ X0 : G, (M.op X0 (τ (τ y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5211 X0 x
       have i₂ := eq5234 X0 x
       grind)
    | exact superpose eq5234 eq5211
    | exact resolve eq5211 eq5234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211 eq5234
  have eq5302 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq5236 X0 x
       have i₂ := eq5240 X0 x
       grind)
    | exact superpose eq5240 eq5236
    | exact resolve eq5236 eq5240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5236 eq5240
  have eq5310 : (σ (M.op x y)) ≠ (M.op (σ x) (τ (τ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5269 (σ x)
       grind)
    | exact superpose eq5269 eq16
    | exact resolve eq16 eq5269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5269
  have eq5323 : ∀ X1 : G, (M.op X1 y) = (M.op X1 (τ (τ y))) := by
    intro X1
    first
    | (have i₁ := eq5259 x X1
       have i₂ := eq5237 X1 x
       grind)
    | exact superpose eq5237 eq5259
    | exact resolve eq5259 eq5237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5237 eq5259
  have eq5370 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq5310
       have i₂ := eq5323 (σ x)
       grind)
    | exact superpose eq5323 eq5310
    | exact resolve eq5310 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5310 eq5323
  have eq5399 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq249 X0 y
       have i₂ := eq5233
       grind)
    | exact superpose eq5233 eq249
    | (have j0 := eq249 X0 y
       grind)
    | (have r₁ := eq249 X0 y
       have r₂ := eq5233
       grind)
    | exact resolve eq249 eq5233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq5411 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq5399 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399
  have eq5434 : ∀ X0 : G, (k (k y y) (k y y)) = (k (k X0 y) (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq311 y X0
       have i₂ := eq5411 X0
       grind)
    | exact superpose eq5411 eq311
    | exact resolve eq311 eq5411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5465 : ∀ X0 : G, (k y y) = (k (k X0 y) (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq5434 X0
       have i₂ := eq5233
       grind)
    | exact superpose eq5233 eq5434
    | exact resolve eq5434 eq5233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5434
  have eq5479 : ∀ X0 : G, y = (k (k X0 y) (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq5465 X0
       have i₂ := eq5233
       grind)
    | exact superpose eq5233 eq5465
    | exact resolve eq5465 eq5233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465
  have eq6134 : (k (τ y) (τ y)) = (M.op (τ y) y) := by
    first
    | (have i₁ := eq246 (τ y)
       have i₂ := eq5302 (τ y)
       grind)
    | exact superpose eq5302 eq246
    | exact resolve eq246 eq5302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5302
  have eq6166 : (τ (k y y)) = (M.op (τ y) y) := by
    first
    | (have i₁ := eq6134
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq6134
    | exact resolve eq6134 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6134
  have eq6184 : (τ y) = (M.op (τ y) y) := by
    first
    | (have i₁ := eq6166
       have i₂ := eq5233
       grind)
    | exact superpose eq5233 eq6166
    | exact resolve eq6166 eq5233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5233 eq6166
  have eq7104 : ∀ X0 : G, (M.op y X0) = (k (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq5411 (M.op X0 y)
       have i₂ := eq5245 y X0
       grind)
    | exact superpose eq5245 eq5411
    | exact resolve eq5411 eq5245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5245
  have eq7105 : ∀ X0 : G, (k X0 y) = (k (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq7104 X0
       have i₂ := eq5411 X0
       grind)
    | exact superpose eq5411 eq7104
    | exact resolve eq7104 eq5411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5411 eq7104
  have eq7711 : ∀ X0 : G, (τ y) ≠ (k (k (τ y) (τ y)) (k (τ y) (τ y))) ∨ (k X0 (k (k (τ y) (τ y)) (k (τ y) (τ y)))) = (M.op (k (k (τ y) (τ y)) (k (τ y) (τ y))) X0) := by
    intro X0
    first
    | (have i₁ := eq308 (τ y) y X0
       have i₂ := eq6184
       grind)
    | exact superpose eq6184 eq308
    | (have j0 := eq308 (τ y) x X0
       grind)
    | exact resolve eq308 eq6184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq6184
  have eq7718 : ∀ X0 : G, (τ y) ≠ (k (k (τ y) (τ y)) (k (τ y) (τ y))) ∨ (M.op (τ y) X0) = (k X0 (τ y)) := by
    intro X0
    grind
  clear eq7711
  have eq7724 : ∀ X0 : G, (τ y) ≠ (k (τ (k y y)) (τ (k y y))) ∨ (M.op (τ y) X0) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq7718 X0
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq7718
    | (have j0 := eq7718 X0
       grind)
    | exact resolve eq7718 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7718
  have eq7729 : ∀ X0 : G, (τ y) ≠ (τ (k (k y y) (k y y))) ∨ (M.op (τ y) X0) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq7724 X0
       have i₂ := eq28 (k y y) (k y y)
       grind)
    | exact superpose eq28 eq7724
    | (have j0 := eq7724 X0
       grind)
    | exact resolve eq7724 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7724
  have eq7733 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (M.op (τ y) X0) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq7729 X0
       have i₂ := eq5479 y
       grind)
    | exact superpose eq5479 eq7729
    | (have j0 := eq7729 X0
       grind)
    | exact resolve eq7729 eq5479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5479 eq7729
  have eq7734 : ∀ X0 : G, (M.op (τ y) X0) = (k X0 (τ y)) := by
    intro X0
    first
    | (have j0 := eq7733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7733
  have eq7736 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k X1 (τ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq5243 X0 X1
       have i₂ := eq7734 X1
       grind)
    | exact superpose eq7734 eq5243
    | exact resolve eq5243 eq7734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5243 eq7734
  have eq11201 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (k X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq7736 X1 (τ X0)
       have i₂ := eq28 y X0
       grind)
    | exact superpose eq28 eq7736
    | exact resolve eq7736 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7736
  have eq14061 : ∀ X0 X1 : G, (M.op X1 (τ (k X0 y))) = (M.op X1 (τ (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq11201 (M.op X0 y) X1
       have i₂ := eq7105 X0
       grind)
    | exact superpose eq7105 eq11201
    | exact resolve eq11201 eq7105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7105
  have eq14195 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14061 X0 X1
       have i₂ := eq11201 X0 X1
       grind)
    | exact superpose eq11201 eq14061
    | exact resolve eq14061 eq11201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11201 eq14061
  have eq15143 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (k (k (M.op X0 y) (M.op X0 y)) (k (M.op X0 y) (M.op X0 y)))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq379 (M.op X0 y)
       have i₂ := eq14195 X0 (τ (k (k (M.op X0 y) (M.op X0 y)) (k (M.op X0 y) (M.op X0 y))))
       grind)
    | exact superpose eq14195 eq379
    | exact resolve eq379 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq14195
  have eq15166 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0)))) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq15143 X0
       have i₂ := eq311 X0 y
       grind)
    | exact superpose eq311 eq15143
    | exact resolve eq15143 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq15143
  have eq15209 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15166 X0
       have i₂ := eq3382 X0 (τ X0)
       grind)
    | exact superpose eq3382 eq15166
    | exact resolve eq15166 eq3382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382 eq15166
  have eq15237 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ X0) (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15209 X0
       have i₂ := eq246 (τ X0)
       grind)
    | exact superpose eq246 eq15209
    | exact resolve eq15209 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq15209
  have eq15252 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15237 X0
       have i₂ := eq5244 (τ X0) (τ X0)
       grind)
    | exact superpose eq5244 eq15237
    | exact resolve eq15237 eq5244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5244 eq15237
  have eq15272 : ∀ X0 : G, (M.op X0 y) = (τ (M.op (σ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq15252 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15252
    | exact resolve eq15252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15252
  have eq15508 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) y)
       have i₂ := eq15272 X0
       grind)
    | exact superpose eq15272 eq11
    | exact resolve eq11 eq15272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15272
  have eq15529 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq5370
       have i₂ := eq15508 x
       grind)
    | exact superpose eq15508 eq5370
    | (have r₁ := eq5370
       have r₂ := eq15508 x
       grind)
    | exact resolve eq5370 eq15508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5370 eq15508
  have eq15535 : False := by grind
  exact eq15535

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pyx_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) (k X0 X1)) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op (M.op X2 X0) (k X0 X1)) X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq596
       grind)
    | exact superpose eq596 eq41
    | exact resolve eq41 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq640 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq639
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq639
    | exact resolve eq639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq642 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq640
    | exact resolve eq640 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq597
    | exact resolve eq597 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq650
       have r₂ := eq27
       grind)
    | exact resolve eq650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq664 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq657 eq187
    | exact resolve eq187 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq664
    | exact resolve eq664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq670 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq657 eq668
    | exact resolve eq668 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq683 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq670 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq670
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq670
       grind)
    | exact resolve eq12 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq720
  have eq726 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq724
    | exact resolve eq724 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq729 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq657 eq726
    | exact resolve eq726 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq800 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq729 eq142
    | exact resolve eq142 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq802 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq800
    | exact resolve eq800 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq800
  have eq810 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq802 eq181
    | exact resolve eq181 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq819 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq670 eq810
    | exact resolve eq810 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq829 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq819 eq108
    | exact resolve eq108 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq819
  have eq836 : y = (k y x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq829
    | exact resolve eq829 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq1318 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq657 eq685
    | (have r₁ := eq685
       have r₂ := eq657
       grind)
    | exact resolve eq685 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657 eq685
  have eq1319 : (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1318
  have eq1320 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq1319
    | exact resolve eq1319 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1321 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq670 eq1320
    | exact resolve eq1320 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq1320
  have eq1332 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1321 eq181
    | exact resolve eq181 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1348 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1332
    | exact resolve eq1332 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1354 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq642 eq1348
    | exact resolve eq1348 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq1348
  have eq1356 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1354
       have r₂ := eq27
       grind)
    | exact resolve eq1354 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1358 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1356 eq29
    | exact resolve eq29 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1365 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1356 eq133
    | exact resolve eq133 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1356
  have eq1372 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99 eq1365
    | exact resolve eq1365 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1365
  have eq1379 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1358
    | exact resolve eq1358 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1380 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq596 eq1372
    | exact resolve eq1372 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq1372
  have eq1383 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1379
       grind)
    | exact superpose eq1379 eq18
    | exact resolve eq18 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1379
       grind)
    | exact superpose eq1379 eq24
    | exact resolve eq24 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1388 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq683
       have i₂ := eq1379
       grind)
    | exact superpose eq1379 eq683
    | (have r₁ := eq683
       have r₂ := eq1379
       grind)
    | exact resolve eq683 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq1389 : (k x (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1388
  have eq1392 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1384
    | exact resolve eq1384 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1427 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1383 eq186
    | exact resolve eq186 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1455 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1427 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq1427
       grind)
    | exact resolve eq12 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1459 : (M.op x y) = (M.op x x) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1455
  have eq1461 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1383 eq1459
    | exact resolve eq1459 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459
  have eq1794 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1461 eq40
    | exact resolve eq40 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1461
  have eq1796 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1794
    | exact resolve eq1794 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1798 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1392 eq1796
    | exact resolve eq1796 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1826 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1798 eq635
    | (have j0 := eq635 (σ y) (σ x)
       grind)
    | exact resolve eq635 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1959 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) y) y) ∨ x = (M.op y x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq601 y x X0
       have i₂ := eq836
       grind)
    | exact superpose eq836 eq601
    | (have j0 := eq601 (M.op (M.op X0 y) y) y x
       grind)
    | exact resolve eq601 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq836
  have eq2009 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) y) y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1959 X0
       have j1 := eq635 (M.op (M.op X0 y) y) y
       grind)
    | (have r₁ := eq1959 X0
       have r₂ := eq635 y x
       grind)
    | exact resolve eq1959 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq2022 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1379 eq2009
    | (have j0 := eq2009 X0
       grind)
    | exact resolve eq2009 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379 eq2009
  have eq2330 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1389 eq1427
    | exact resolve eq1427 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389 eq1427
  have eq2339 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq2330
  have eq2345 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2339 eq42
    | exact resolve eq42 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2339
  have eq2349 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2345
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2345
    | exact resolve eq2345 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2351 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1392 eq2349
    | exact resolve eq2349 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq2357 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2351 eq597
    | exact resolve eq597 eq2351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351
  have eq2379 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2357 eq181
    | exact resolve eq181 eq2357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq2393 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1383 eq2379
    | exact resolve eq2379 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383 eq2379
  have eq2412 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2393 eq36
    | exact resolve eq36 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2393
  have eq2421 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2412
    | exact resolve eq2412 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412
  have eq2423 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1392 eq2421
    | exact resolve eq2421 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq2448 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2423 eq597
    | exact resolve eq597 eq2423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq2423
  have eq2457 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2448
  have eq2468 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2457 eq27
    | exact resolve eq27 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2479 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2468
       have r₂ := eq1392
       grind)
    | exact resolve eq2468 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2484 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2479 eq27
    | exact resolve eq27 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2485 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2479 eq176
    | exact resolve eq176 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2486 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2479 eq179
    | exact resolve eq179 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2487 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2479 eq187
    | exact resolve eq187 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq2493 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2487
       have i₂ := eq181 sF2
       grind)
    | exact superpose eq181 eq2487
    | exact resolve eq2487 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq2494 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1392 eq2484
    | exact resolve eq2484 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq2484
  have eq2497 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq2494
  have eq2504 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2493 eq142
    | exact resolve eq142 eq2493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq2493
  have eq2511 : x = (k (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2504
    | exact resolve eq2504 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq2523 : x ≠ x ∨ x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2511 eq635
    | (have j0 := eq635 (τ (M.op (σ x) (σ x))) x
       grind)
    | (have r₁ := eq635 (τ (M.op (σ x) (σ x))) x
       have r₂ := eq2511
       grind)
    | exact resolve eq635 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511
  have eq2524 : x = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by grind
  clear eq2523
  have eq2548 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (k (σ y) X0)) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2485 x
       have i₂ := eq28 sF3 x
       grind)
    | exact superpose eq28 eq2485
    | (have j1 := eq28 (M.op (σ x) (k (σ y) X0)) (σ y)
       grind)
    | exact resolve eq2485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2586 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2486 eq2486
    | exact resolve eq2486 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq2602 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2586
  have eq2625 : x = (M.op (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2602 eq2524
    | exact resolve eq2524 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524
  have eq2641 : x = (M.op (τ (σ x)) x) ∨ x = (M.op x y) := by grind
  clear eq2625
  have eq2647 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2641
    | exact resolve eq2641 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2641
  have eq4885 : y = (M.op (M.op (M.op x y) y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2022 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2022
    | (have j0 := eq2022 x
       grind)
    | exact resolve eq2022 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq5096 : y = (M.op (k (M.op x y) y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq4885
       have i₂ := eq28 sF0 y
       grind)
    | exact superpose eq28 eq4885
    | (have j1 := eq28 (k (M.op x y) y) y
       grind)
    | exact resolve eq4885 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4885
  have eq5120 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1380 eq5096
    | exact resolve eq5096 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380 eq5096
  have eq5121 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq5120
  have eq5134 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5121 eq177
    | exact resolve eq177 eq5121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq5146 : y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5121 eq5134
    | exact resolve eq5134 eq5121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5121 eq5134
  have eq5147 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq5146
  have eq8033 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1798 eq2548
    | (have j0 := eq2548 (σ x)
       grind)
    | exact resolve eq2548 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798 eq2548
  have eq8068 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq8033
  have eq8074 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq8068
    | exact resolve eq8068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8068
  have eq8077 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2479 eq8074
    | exact resolve eq8074 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8074
  have eq8078 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq8077
    | exact resolve eq8077 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8077
  have eq8079 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2479 eq8078
    | exact resolve eq8078 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8078
  have eq8080 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq8079
       have r₂ := eq1826
       grind)
    | exact resolve eq8079 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826 eq8079
  have eq8085 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq8080 eq2485
    | exact resolve eq2485 eq8080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485 eq8080
  have eq8123 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq8085
  have eq8144 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2602 eq8123
    | exact resolve eq8123 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602 eq8123
  have eq8149 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq8144
    | exact resolve eq8144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8144
  have eq8154 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2479 eq8149
    | exact resolve eq8149 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479 eq8149
  have eq8158 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8154
       have r₂ := eq2497
       grind)
    | exact resolve eq8154 eq2497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497 eq8154
  have eq8164 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2647
       have i₂ := eq8158
       grind)
    | exact superpose eq8158 eq2647
    | exact resolve eq2647 eq8158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647 eq8158
  have eq8194 : x = (M.op x y) := by grind
  clear eq8164
  have eq8202 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8194
       grind)
    | exact superpose eq8194 eq18
    | exact resolve eq18 eq8194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8203 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq8194
       grind)
    | exact superpose eq8194 eq22
    | exact resolve eq22 eq8194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8194
  have eq8216 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8203 eq20
    | exact resolve eq20 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8287 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8202 eq5147
    | exact resolve eq5147 eq8202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5147
  have eq8319 : y = (M.op x y) := by grind
  clear eq8287
  have eq8328 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8319
       grind)
    | exact superpose eq8319 eq24
    | exact resolve eq24 eq8319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8334 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8202
       have i₂ := eq8319
       grind)
    | exact superpose eq8319 eq8202
    | exact resolve eq8202 eq8319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8202 eq8319
  have eq8339 : (σ x) = (σ y) := by
    first
    | exact superpose eq8203 eq8328
    | exact resolve eq8328 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8203 eq8328
  have eq8341 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8339 eq26
    | exact resolve eq26 eq8339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8339
  have eq8471 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8334 eq181
    | exact resolve eq181 eq8334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq8489 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8334 eq8471
    | exact resolve eq8471 eq8334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8334 eq8471
  have eq8551 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8489 eq38
    | exact resolve eq38 eq8489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq8489
  have eq8568 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq8551
    | exact resolve eq8551 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8551
  have eq8570 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq8216 eq8568
    | exact resolve eq8568 eq8216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8568
  have eq8587 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8570 eq635
    | (have j0 := eq635 (σ x) (σ x)
       grind)
    | (have r₁ := eq635 (σ x) (σ x)
       have r₂ := eq8570
       grind)
    | exact resolve eq635 eq8570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq8570
  have eq8588 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8587
  have eq8618 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8588 eq8341
    | exact resolve eq8341 eq8588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8341 eq8588
  have eq8662 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8618 eq27
    | exact resolve eq27 eq8618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8618
  have eq8678 : False := by grind
  exact eq8678

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq78 (σ X0)
       grind)
    | exact superpose eq78 eq15
    | exact resolve eq15 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq83
    | exact resolve eq83 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq83
  have eq111 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq112 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq111
    | exact resolve eq111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq112
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq222 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq225 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq220 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq220
    | (have j0 := eq220 X0 X1
       grind)
    | exact resolve eq220 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq1973 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq222 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq222
    | exact resolve eq222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2032 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1973 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1973
    | (have j0 := eq1973 X0 X1
       grind)
    | exact resolve eq1973 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq2700 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq225 x y
       grind)
    | exact superpose eq225 eq16
    | (have j1 := eq225 x y
       grind)
    | exact resolve eq16 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq8606 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2700
       have i₂ := eq2032 x y
       grind)
    | exact superpose eq2032 eq2700
    | (have j1 := eq2032 x y
       grind)
    | (have r₁ := eq2700
       have r₂ := eq2032 x y
       grind)
    | (have r₁ := eq2700
       have r₂ := eq2032 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2700
       have r₂ := eq2032 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2700 eq2032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032 eq2700
  have eq8607 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq8606
  have eq8609 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8607
       grind)
    | exact superpose eq8607 eq16
    | exact resolve eq16 eq8607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8607
  have eq8610 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8609
       have r₂ := eq90 x
       grind)
    | exact resolve eq8609 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8609
  have eq8612 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8610
       grind)
    | exact superpose eq8610 eq10
    | exact resolve eq10 eq8610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8610
  have eq8681 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq8612
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8612
    | exact resolve eq8612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8612
  have eq8684 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8681
       grind)
    | exact superpose eq8681 eq16
    | exact resolve eq16 eq8681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8681
  have eq8685 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq8684
       have r₂ := eq90 x
       grind)
    | exact resolve eq8684 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq8684
  have eq8695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq115 y
       have i₂ := eq8685
       grind)
    | exact superpose eq8685 eq115
    | exact resolve eq115 eq8685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8685
  have eq8754 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq8695
       have r₂ := eq16
       grind)
    | exact resolve eq8695 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8695
  have eq8776 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq8754
       grind)
    | exact superpose eq8754 eq10
    | exact resolve eq10 eq8754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8754
  have eq8845 : x = (M.op y y) := by
    first
    | (have i₁ := eq8776
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8776
    | exact resolve eq8776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq8859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq115 y
       have i₂ := eq8845
       grind)
    | exact superpose eq8845 eq115
    | exact resolve eq115 eq8845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq8845
  have eq8918 : False := by grind
  exact eq8918
