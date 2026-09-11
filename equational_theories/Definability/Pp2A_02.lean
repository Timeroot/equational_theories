import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxy_pxx_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
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
       have r₂ := eq12 x x
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
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq189 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq218 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq189
  have eq223 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq218 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq218 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq218 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq226 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq223
    | (have j0 := eq223 X0 X1
       grind)
    | exact resolve eq223 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq223
  have eq567 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq226
    | exact resolve eq226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq226 (σ X0) X1
       grind)
    | exact superpose eq226 eq15
    | (have j1 := eq226 (σ X0) X1
       grind)
    | exact resolve eq15 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq589 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq604 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq567 (τ X1) X0
       grind)
    | exact superpose eq567 eq18
    | (have j1 := eq567 (τ X1) X0
       grind)
    | exact resolve eq18 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1996 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq604 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq604
    | exact resolve eq604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq2043 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1996 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1996
    | (have j0 := eq1996 X0 X1
       grind)
    | exact resolve eq1996 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq5262 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq589 x y
       grind)
    | exact superpose eq589 eq16
    | (have j1 := eq589 x y
       grind)
    | exact resolve eq16 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq5370 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5262
       have i₂ := eq2043 y x
       grind)
    | exact superpose eq2043 eq5262
    | (have j1 := eq2043 y x
       grind)
    | (have r₁ := eq5262
       have r₂ := eq2043 y x
       grind)
    | exact resolve eq5262 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043 eq5262
  have eq5371 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5370
  have eq5374 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq5371
       grind)
    | exact superpose eq5371 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5371
       grind)
    | exact resolve eq13 eq5371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5375 : y ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5371
       grind)
    | exact superpose eq5371 eq12
    | exact resolve eq12 eq5371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5371
  have eq5376 : (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5374
  have eq5377 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq5376
       have r₂ := eq5375
       grind)
    | exact resolve eq5376 eq5375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5375 eq5376
  have eq5509 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5377
       grind)
    | exact superpose eq5377 eq16
    | exact resolve eq16 eq5377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5511 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq5377
       grind)
    | exact superpose eq5377 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq5377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5512 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq5377
       grind)
    | exact superpose eq5377 eq12
    | exact resolve eq12 eq5377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq5513 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq5512
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5512
    | exact resolve eq5512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5512
  have eq5514 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq5511
       have r₂ := eq67 x
       grind)
    | exact resolve eq5511 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511
  have eq5515 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq5514
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5514
    | exact resolve eq5514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5514
  have eq5516 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq5515
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq5515
    | exact resolve eq5515 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq5515
  have eq5517 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5516
       have r₂ := eq5513
       grind)
    | exact resolve eq5516 eq5513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5513 eq5516
  have eq5627 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5517
       have i₂ := eq567 y x
       grind)
    | exact superpose eq567 eq5517
    | (have j1 := eq567 y x
       grind)
    | exact resolve eq5517 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5632 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq5517
       grind)
    | exact superpose eq5517 eq210
    | (have j0 := eq210 x y
       grind)
    | (have r₁ := eq210 x y
       have r₂ := eq5517
       grind)
    | exact resolve eq210 eq5517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq5642 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq5632
  have eq5645 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq5627
  have eq5647 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq210 x y
       grind)
    | (have r₁ := eq5642
       have r₂ := eq210 x y
       grind)
    | exact resolve eq5642 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq5642
  have eq5712 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5509
       have i₂ := eq5645
       grind)
    | exact superpose eq5645 eq5509
    | (have r₁ := eq5509
       have r₂ := eq5645
       grind)
    | exact resolve eq5509 eq5645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5645
  have eq5716 : (k x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq5712
  have eq5719 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq5716
       have r₂ := eq5509
       grind)
    | exact resolve eq5716 eq5509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509 eq5716
  have eq5728 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq567 y x
       have i₂ := eq5719
       grind)
    | exact superpose eq5719 eq567
    | (have j0 := eq567 y x
       grind)
    | exact resolve eq567 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq5735 : (M.op x y) = (M.op x x) := by grind
  clear eq5728
  have eq5996 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq5647
       grind)
    | exact superpose eq5647 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq5647
       grind)
    | exact resolve eq12 eq5647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5997 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5647
  have eq5998 : (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5996
  have eq5999 : (σ y) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5998
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5998
    | exact resolve eq5998 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5998
  have eq6006 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5999
       have i₂ := eq5719
       grind)
    | exact superpose eq5719 eq5999
    | exact resolve eq5999 eq5719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5719 eq5999
  have eq6012 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6006
       have r₂ := eq5997
       grind)
    | exact resolve eq6006 eq5997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5997 eq6006
  have eq6021 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6012
       grind)
    | exact superpose eq6012 eq16
    | exact resolve eq16 eq6012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6012
  have eq6027 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6021
       have i₂ := eq5735
       grind)
    | exact superpose eq5735 eq6021
    | exact resolve eq6021 eq5735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5735 eq6021
  have eq6028 : False := by grind
  exact eq6028

/-- `Equation115`: `x = y ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation115 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law115 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law115.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq164 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq167
       have i₂ := eq164 sF3
       grind)
    | exact superpose eq164 eq167
    | exact resolve eq167 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq179 : (M.op x y) = (k y y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq166
       have i₂ := eq164 y
       grind)
    | exact superpose eq164 eq166
    | exact resolve eq166 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq850 : ∀ X0 X1 : G, (k X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16366 : (M.op x y) ≠ (k y y) ∨ x = y ∨ (k x y) = (k y y) := by
    first
    | (have i₁ := eq850 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq850
    | (have j0 := eq850 y x
       grind)
    | exact resolve eq850 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16367 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq850
    | (have j0 := eq850 (σ y) (σ x)
       grind)
    | exact resolve eq850 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq17522 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq16366
       have i₂ := eq179
       grind)
    | exact superpose eq179 eq16366
    | (have r₁ := eq16366
       have r₂ := eq179
       grind)
    | exact resolve eq16366 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq16366
  have eq17523 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq17522
  have eq17524 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq17523
  have eq17530 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq17524
       grind)
    | exact superpose eq17524 eq41
    | exact resolve eq41 eq17524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq17524
  have eq17532 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq17530
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17530
    | exact resolve eq17530 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17530
  have eq17536 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq17532
    | exact resolve eq17532 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17532
  have eq17671 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq178 eq16367
    | (have r₁ := eq16367
       have r₂ := eq178
       grind)
    | exact resolve eq16367 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq16367
  have eq17672 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq17671
  have eq17673 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq17672
  have eq17680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17673 eq17536
    | exact resolve eq17536 eq17673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17536 eq17673
  have eq17685 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17680
       have r₂ := eq27
       grind)
    | exact resolve eq17680 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17680
  have eq17688 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17685 eq31
    | exact resolve eq31 eq17685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17685
  have eq17789 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq17688
    | exact resolve eq17688 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17688
  have eq17790 : x = y := by grind
  clear eq17789
  have eq17795 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17790
       grind)
    | exact superpose eq17790 eq18
    | exact resolve eq18 eq17790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq17796 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17790
       grind)
    | exact superpose eq17790 eq24
    | exact resolve eq24 eq17790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17790
  have eq17832 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17796
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17796
    | exact resolve eq17796 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17796
  have eq17833 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq17795
       have i₂ := eq164 x
       grind)
    | exact superpose eq164 eq17795
    | exact resolve eq17795 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17795
  have eq17834 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17832 eq26
    | exact resolve eq26 eq17832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17832
  have eq17932 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17834
       have i₂ := eq164 sF2
       grind)
    | exact superpose eq164 eq17834
    | exact resolve eq17834 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq17834
  have eq17936 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq17833
       grind)
    | exact superpose eq17833 eq40
    | exact resolve eq40 eq17833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17833
  have eq17968 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17936
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17936
    | exact resolve eq17936 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17936
  have eq17978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17932 eq17968
    | exact resolve eq17968 eq17932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17932 eq17968
  have eq17984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17978
    | exact resolve eq17978 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq17978
  have eq17987 : False := by grind
  exact eq17987

/-- `Equation115`: `x = y ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation115 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law115 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law115.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq572 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq787 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq796 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq779 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq779
    | (have j0 := eq779 X0 X1
       grind)
    | exact resolve eq779 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq3601 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq796 x y
       grind)
    | exact superpose eq796 eq16
    | (have j1 := eq796 x y
       grind)
    | exact resolve eq16 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3608 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq796 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq5751 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq787 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq787
    | exact resolve eq787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq5887 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5751 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5751
    | (have j0 := eq5751 X0 X1
       grind)
    | exact resolve eq5751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5751
  have eq10032 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3601
       have i₂ := eq5887 y x
       grind)
    | exact superpose eq5887 eq3601
    | (have j1 := eq5887 y x
       grind)
    | (have r₁ := eq3601
       have r₂ := eq5887 y x
       grind)
    | (have r₁ := eq3601
       have r₂ := eq5887 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3601
       have r₂ := eq5887 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3601 eq5887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601 eq5887
  have eq10033 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq10032
  have eq11085 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3608 (τ X1) (τ X0)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq3608
    | (have j0 := eq3608 (τ X1) (τ X0)
       grind)
    | exact resolve eq3608 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq11143 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11085 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq11085
    | (have j0 := eq11085 X0 X1
       grind)
    | exact resolve eq11085 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11085
  have eq11178 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11143 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11143
    | (have j0 := eq11143 X0 X1
       grind)
    | exact resolve eq11143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11143
  have eq11210 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11178 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11178
    | (have j0 := eq11178 X0 X1
       grind)
    | exact resolve eq11178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11178
  have eq11236 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11210 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11210
    | (have j0 := eq11210 X0 X1
       grind)
    | exact resolve eq11210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11210
  have eq11256 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11236 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq11236
    | (have j0 := eq11236 X0 X1
       grind)
    | exact resolve eq11236 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11236
  have eq11275 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11256 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11256
    | (have j0 := eq11256 X0 X1
       grind)
    | exact resolve eq11256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11256
  have eq11288 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11275 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11275
    | (have j0 := eq11275 X0 X1
       grind)
    | exact resolve eq11275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11275
  have eq19487 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10033
       grind)
    | exact superpose eq10033 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10033
       grind)
    | exact resolve eq13 eq10033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10033
  have eq19488 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq19487
  have eq19489 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq19488
  have eq22557 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19489
       grind)
    | exact superpose eq19489 eq16
    | exact resolve eq16 eq19489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19489
  have eq22558 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq22557
       have r₂ := eq23 x
       grind)
    | exact resolve eq22557 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22557
  have eq22561 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq572 x (σ y)
       have i₂ := eq22558
       grind)
    | exact superpose eq22558 eq572
    | (have j0 := eq572 x (σ y)
       grind)
    | (have r₁ := eq572 x (σ y)
       have r₂ := eq22558
       grind)
    | exact resolve eq572 eq22558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22558
  have eq22568 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq22561
  have eq22569 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq22568
  have eq22572 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22569
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq22569
    | exact resolve eq22569 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22569
  have eq22657 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3608 x y
       have i₂ := eq22572
       grind)
    | exact superpose eq22572 eq3608
    | (have j0 := eq3608 x y
       grind)
    | (have r₁ := eq3608 x y
       have r₂ := eq22572
       grind)
    | exact resolve eq3608 eq22572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22572
  have eq22683 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq22657
  have eq22684 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq22683
  have eq22688 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq3608 x y
       grind)
    | (have r₁ := eq22684
       have r₂ := eq3608 x y
       grind)
    | exact resolve eq22684 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608 eq22684
  have eq22691 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22688
       grind)
    | exact superpose eq22688 eq16
    | exact resolve eq16 eq22688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22692 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq572 x (σ y)
       have i₂ := eq22688
       grind)
    | exact superpose eq22688 eq572
    | (have j0 := eq572 x (σ y)
       grind)
    | (have r₁ := eq572 x (σ y)
       have r₂ := eq22688
       grind)
    | exact resolve eq572 eq22688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq22688
  have eq22699 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq22692
  have eq22700 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq22699
  have eq22703 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22700
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq22700
    | exact resolve eq22700 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22700
  have eq22710 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22703
       grind)
    | exact superpose eq22703 eq10
    | exact resolve eq10 eq22703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22703
  have eq22906 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22710
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22710
    | exact resolve eq22710 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22710
  have eq22908 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22906
       grind)
    | exact superpose eq22906 eq16
    | exact resolve eq16 eq22906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22906
  have eq22909 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq22908
       have r₂ := eq23 x
       grind)
    | exact resolve eq22908 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22908
  have eq22921 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq22909
       grind)
    | exact superpose eq22909 eq10
    | exact resolve eq10 eq22909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22909
  have eq23119 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq22921
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq22921
    | exact resolve eq22921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22921
  have eq23143 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11288 y x
       have i₂ := eq23119
       grind)
    | exact superpose eq23119 eq11288
    | (have j0 := eq11288 y x
       grind)
    | (have r₁ := eq11288 y x
       have r₂ := eq23119
       grind)
    | exact resolve eq11288 eq23119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11288 eq23119
  have eq23150 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq23143
  have eq23154 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22691
       have i₂ := eq23150
       grind)
    | exact superpose eq23150 eq22691
    | exact resolve eq22691 eq23150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22691 eq23150
  have eq23160 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq23154
  have eq23161 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23160
       grind)
    | exact superpose eq23160 eq16
    | exact resolve eq16 eq23160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23160
  have eq23164 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq23161
       have r₂ := eq23 x
       grind)
    | exact resolve eq23161 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23161
  have eq23165 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23164
       grind)
    | exact superpose eq23164 eq16
    | exact resolve eq16 eq23164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23166 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23164
       grind)
    | exact superpose eq23164 eq10
    | exact resolve eq10 eq23164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23164
  have eq23362 : x = y := by
    first
    | (have i₁ := eq23166
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23166
    | exact resolve eq23166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23166
  have eq23363 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq23165
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq23165
    | exact resolve eq23165 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23165
  have eq23364 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq23363
       have i₂ := eq23362
       grind)
    | exact superpose eq23362 eq23363
    | exact resolve eq23363 eq23362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23362 eq23363
  have eq23365 : False := by grind
  exact eq23365

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq90
    | exact resolve eq90 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq90
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq101
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq118 X0 X1
       grind)
    | (have r₁ := eq134 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq134 X0 (σ (M.op X0 X0))
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq134 (M.op X0 X0) (σ X0)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq134 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq134
  have eq163 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq141 X1 (σ X0)
       grind)
    | exact superpose eq141 eq15
    | (have j1 := eq141 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq175 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq163 (τ X1) X0
       grind)
    | exact superpose eq163 eq19
    | (have j1 := eq163 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq163
  have eq259 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq175
    | exact resolve eq175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq259
    | (have j0 := eq259 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq834 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq168 x y
       grind)
    | exact superpose eq168 eq16
    | (have j1 := eq168 x y
       grind)
    | exact resolve eq16 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq846 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq834
       have i₂ := eq282 y x
       grind)
    | exact superpose eq282 eq834
    | (have j1 := eq282 (σ x) (σ y)
       grind)
    | (have r₁ := eq834
       have r₂ := eq282 y x
       grind)
    | (have r₁ := eq834
       have r₂ := eq282 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq834
       have r₂ := eq282 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq834 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq834
  have eq847 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq846
  have eq849 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq847
       grind)
    | exact superpose eq847 eq16
    | exact resolve eq16 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq850 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq849
       have r₂ := eq101 x
       grind)
    | exact resolve eq849 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq851 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq850
       grind)
    | exact superpose eq850 eq16
    | exact resolve eq16 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq850
       grind)
    | exact superpose eq850 eq10
    | exact resolve eq10 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq893 : x = y := by
    first
    | (have i₁ := eq852
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq852
    | exact resolve eq852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq894 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq851
       have i₂ := eq101 x
       grind)
    | exact superpose eq101 eq851
    | exact resolve eq851 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq851
  have eq895 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq894
       have i₂ := eq893
       grind)
    | exact superpose eq893 eq894
    | exact resolve eq894 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq894
  have eq896 : False := by grind
  exact eq896

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_x_pxy_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq175 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq180 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq181
    | exact resolve eq181 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq984 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq710 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq1183 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) (M.op X0 (M.op (M.op (M.op x y) X0) y))) := by
    intro X0
    first
    | exact superpose eq176 eq184
    | exact resolve eq184 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1184 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (M.op X0 (M.op (M.op (M.op x y) X0) y))) := by
    intro X0
    first
    | exact superpose eq177 eq184
    | exact resolve eq184 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1214 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq176 eq1184
    | exact resolve eq1184 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1215 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) X0) := by
    intro X0
    first
    | exact superpose eq176 eq1183
    | exact resolve eq1183 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1261 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 x y X0 X1
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq178
    | (have j0 := eq178 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq178 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq652
       grind)
    | exact superpose eq652 eq39
    | exact resolve eq39 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq1316 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1315
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1315
    | exact resolve eq1315 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1318 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1316
    | exact resolve eq1316 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq3586 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ y) X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1214 eq178
    | exact resolve eq178 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq4545 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X1) (M.op (M.op (M.op x y) X0) y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1215 eq178
    | exact resolve eq178 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1215
  have eq13756 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq3586
    | exact resolve eq3586 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq13876 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq13756 eq13
    | (have j0 := eq13 X0 (M.op (σ y) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (σ y) X0)
       have r₂ := eq13756 X0
       grind)
    | exact resolve eq13 eq13756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13889 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)))) := by
    intro X0
    first
    | exact superpose eq13756 eq723
    | exact resolve eq723 eq13756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq13937 : ∀ X0 : G, (k X0 (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13876 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13876
  have eq13947 : ∀ X0 : G, (M.op (σ y) X0) = (k (M.op (σ y) X0) X0) := by
    intro X0
    first
    | exact superpose eq177 eq13889
    | exact resolve eq13889 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq13889
  have eq14001 : (τ (σ x)) = (k x (τ (M.op (σ y) (σ x)))) := by
    first
    | exact superpose eq13937 eq90
    | exact resolve eq90 eq13937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq13937
  have eq14004 : x = (k x (τ (M.op (σ y) (σ x)))) := by
    first
    | exact superpose eq29 eq14001
    | exact resolve eq14001 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14001
  have eq14239 : (τ (M.op (σ y) (σ x))) = (k (τ (M.op (σ y) (σ x))) x) := by
    first
    | exact superpose eq13947 eq141
    | exact resolve eq141 eq13947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13947
  have eq18700 : ∀ X0 : G, (M.op X0 (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq176 eq4545
    | exact resolve eq4545 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq4545
  have eq18858 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op y X0)
       have i₂ := eq18700 X0
       grind)
    | exact superpose eq18700 eq13
    | (have j0 := eq13 X0 (M.op y X0)
       grind)
    | (have r₁ := eq13 X0 (M.op y X0)
       have r₂ := eq18700 X0
       grind)
    | exact resolve eq13 eq18700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18880 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op X0 x) (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq1261 X0 (M.op y X0)
       have i₂ := eq18700 X0
       grind)
    | exact superpose eq18700 eq1261
    | exact resolve eq1261 eq18700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq18881 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq1263 X0 (M.op y X0)
       have i₂ := eq18700 X0
       grind)
    | exact superpose eq18700 eq1263
    | exact resolve eq1263 eq18700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq18939 : ∀ X0 : G, (k X0 (M.op y X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq18858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18858
  have eq19011 : (σ x) = (k (σ x) (σ (M.op y x))) := by
    first
    | (have i₁ := eq35 (M.op y x)
       have i₂ := eq18939 x
       grind)
    | exact superpose eq18939 eq35
    | exact resolve eq35 eq18939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq18939
  have eq19022 : (σ x) = (k (σ x) (σ (M.op y x))) := by
    first
    | (have i₁ := eq19011
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19011
    | exact resolve eq19011 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19011
  have eq51614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1318 eq653
    | exact resolve eq653 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51625 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq51614
       have r₂ := eq27
       grind)
    | exact resolve eq51614 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51614
  have eq51683 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq51625 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq51625
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq51625
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq51625
       grind)
    | exact resolve eq12 eq51625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51724 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq51625
  have eq51729 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq51683
       have r₂ := eq51724
       grind)
    | exact resolve eq51683 eq51724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51683 eq51724
  have eq51733 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq51729
       have r₂ := eq26
       grind)
    | exact resolve eq51729 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51729
  have eq51736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1318 eq51733
    | exact resolve eq51733 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51733
  have eq51738 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq51736
       have r₂ := eq27
       grind)
    | exact resolve eq51736 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51736
  have eq51745 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq51738 eq14239
    | exact resolve eq14239 eq51738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51763 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq51738 eq13756
    | exact resolve eq13756 eq51738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51793 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq51738 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq51738
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq51738
       grind)
    | exact resolve eq13 eq51738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51738
  have eq51831 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by grind
  clear eq51793
  have eq51860 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq51763
    | exact resolve eq51763 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51763
  have eq51865 : y = (k y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq51745
    | exact resolve eq51745 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51745
  have eq51884 : (M.op x y) = (M.op y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq51865
       have r₂ := eq13 y x
       grind)
    | exact resolve eq51865 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51865
  have eq51941 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq51884
       grind)
    | exact superpose eq51884 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq51884
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq51884
       grind)
    | exact resolve eq12 eq51884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51943 : y ≠ (M.op x y) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq51884
       grind)
    | exact superpose eq51884 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq51884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51884
  have eq51982 : y ≠ (M.op x y) ∨ y = (k y x) := by grind
  clear eq51943
  have eq51986 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq51941
       have r₂ := eq51982
       grind)
    | exact resolve eq51941 eq51982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51941 eq51982
  have eq51993 : (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq51986
       have r₂ := eq18
       grind)
    | exact resolve eq51986 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51986
  have eq52172 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq51993
       grind)
    | exact superpose eq51993 eq39
    | exact resolve eq39 eq51993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51993
  have eq52177 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq52172
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52172
    | exact resolve eq52172 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52172
  have eq52181 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq52177
    | exact resolve eq52177 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52177
  have eq52227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq52181 eq653
    | exact resolve eq653 eq52181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52238 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq52227
       have r₂ := eq27
       grind)
    | exact resolve eq52227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52227
  have eq52522 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18700 x
       have i₂ := eq51860
       grind)
    | exact superpose eq51860 eq18700
    | exact resolve eq18700 eq51860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52551 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq51860
       grind)
    | exact superpose eq51860 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq51860
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq51860
       grind)
    | exact resolve eq12 eq51860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52592 : y ≠ (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq51860
  have eq52596 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq52551
       have r₂ := eq52592
       grind)
    | exact resolve eq52551 eq52592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52551
  have eq52603 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq52596
       have r₂ := eq18
       grind)
    | exact resolve eq52596 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52596
  have eq52613 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq19022
       have i₂ := eq52522
       grind)
    | exact superpose eq52522 eq19022
    | exact resolve eq19022 eq52522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52522
  have eq52740 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq52613
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq52613
    | exact resolve eq52613 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52613
  have eq52760 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have r₁ := eq52740
       have r₂ := eq175
       grind)
    | exact resolve eq52740 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52740
  have eq52772 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq52760 eq152
    | exact resolve eq152 eq52760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52760
  have eq52776 : x = (k x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq29 eq52772
    | exact resolve eq52772 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52772
  have eq58114 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq51831 eq1318
    | exact resolve eq1318 eq51831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq51831
  have eq58122 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq58114
  have eq58193 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq58122
       grind)
    | exact superpose eq58122 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq58122
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq58122
       grind)
    | exact resolve eq12 eq58122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58237 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq58122
  have eq58241 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq58193
       have r₂ := eq58237
       grind)
    | exact resolve eq58193 eq58237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58193
  have eq58248 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq58241
       have r₂ := eq18
       grind)
    | exact resolve eq58241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58241
  have eq68206 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq52238 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq52238
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq52238
       grind)
    | exact resolve eq12 eq52238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68258 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq52238
  have eq68264 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq68206
       have r₂ := eq68258
       grind)
    | exact resolve eq68206 eq68258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68206 eq68258
  have eq68268 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq68264
       have r₂ := eq26
       grind)
    | exact resolve eq68264 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68264
  have eq68271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq52181 eq68268
    | exact resolve eq68268 eq52181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52181 eq68268
  have eq68273 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq68271
       have r₂ := eq27
       grind)
    | exact resolve eq68271 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68271
  have eq68281 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y x) := by
    first
    | exact superpose eq68273 eq14239
    | exact resolve eq14239 eq68273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14239 eq68273
  have eq68418 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq31 eq68281
    | exact resolve eq68281 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68281
  have eq68419 : y = (k y x) := by grind
  clear eq68418
  have eq68450 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq52603
       have i₂ := eq68419
       grind)
    | exact superpose eq68419 eq52603
    | exact resolve eq52603 eq68419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52603
  have eq68451 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq58248
       have i₂ := eq68419
       grind)
    | exact superpose eq68419 eq58248
    | exact resolve eq58248 eq68419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58248
  have eq68454 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq68419
       grind)
    | exact superpose eq68419 eq39
    | exact resolve eq39 eq68419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68419
  have eq68459 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq68454
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq68454
    | exact resolve eq68454 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68454
  have eq68462 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq68451
       have r₂ := eq58237
       grind)
    | exact resolve eq68451 eq58237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58237 eq68451
  have eq68463 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq68450
       have r₂ := eq52592
       grind)
    | exact resolve eq68450 eq52592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52592 eq68450
  have eq68480 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq68459 eq653
    | exact resolve eq653 eq68459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq68552 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18700 x
       have i₂ := eq68462
       grind)
    | exact superpose eq68462 eq18700
    | exact resolve eq18700 eq68462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68462
  have eq68666 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68552
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq68552
    | exact resolve eq68552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68552
  have eq68699 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq68666 eq28
    | exact resolve eq28 eq68666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq68859 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq68699
    | exact resolve eq68699 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq68699
  have eq68877 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq68859
       grind)
    | exact superpose eq68859 eq18
    | exact resolve eq18 eq68859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq69080 : (σ x) = (k (σ x) (σ (M.op (M.op x y) x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19022
       have i₂ := eq68859
       grind)
    | exact superpose eq68859 eq19022
    | exact resolve eq19022 eq68859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69180 : x = (k x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52776
       have i₂ := eq68859
       grind)
    | exact superpose eq68859 eq52776
    | exact resolve eq52776 eq68859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52776
  have eq69257 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq69180
       have r₂ := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq69180
       have r₂ := eq13 x y
       grind)
    | exact resolve eq69180 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69180
  have eq69330 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19022
       have i₂ := eq68463
       grind)
    | exact superpose eq68463 eq19022
    | exact resolve eq19022 eq68463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19022 eq68463
  have eq69474 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69330
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq69330
    | exact resolve eq69330 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq69330
  have eq69497 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq69474
       have r₂ := eq175
       grind)
    | exact resolve eq69474 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq69474
  have eq69513 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | exact superpose eq69497 eq152
    | exact resolve eq152 eq69497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq69517 : x = (k x y) := by
    first
    | exact superpose eq29 eq69513
    | exact resolve eq69513 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69513
  have eq71928 : (M.op x y) ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq68877 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq68877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71985 : (M.op x y) ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq71928
  have eq72013 : (M.op x y) ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq69257 eq71985
    | exact resolve eq71985 eq69257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71985
  have eq72014 : (M.op x y) ≠ (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq72013
  have eq76142 : (σ x) = (k (σ x) (σ (k x (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq69080
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq69080
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq69080 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69080
  have eq76169 : (σ x) = (k (σ x) (k (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq41 eq76142
    | exact resolve eq76142 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq76142
  have eq76174 : (σ x) = (k (σ x) (k (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq76169
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq76169
    | exact resolve eq76169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76169
  have eq76178 : (σ x) = (k (σ x) (k (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq68666 eq76174
    | exact resolve eq76174 eq68666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68666 eq76174
  have eq76181 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq69497 eq76178
    | exact resolve eq76178 eq69497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76178
  have eq76182 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq68877 eq76181
    | exact resolve eq76181 eq68877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76181
  have eq76183 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have r₁ := eq76182
       have r₂ := eq72014
       grind)
    | exact resolve eq76182 eq72014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76182
  have eq76184 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq68877 eq76183
    | exact resolve eq76183 eq68877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76183
  have eq76185 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq76184
  have eq76190 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76185 eq141
    | exact resolve eq141 eq76185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq76185
  have eq76197 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq76190
    | exact resolve eq76190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq76190
  have eq76350 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq984 x
       have i₂ := eq76197
       grind)
    | exact superpose eq76197 eq984
    | (have j0 := eq984 x
       grind)
    | (have r₁ := eq984 x
       have r₂ := eq76197
       grind)
    | exact resolve eq984 eq76197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76197
  have eq76351 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq76350
  have eq76370 : y = (M.op y (M.op (M.op x y) (M.op x (M.op y x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18880 x
       have i₂ := eq76351
       grind)
    | exact superpose eq76351 eq18880
    | exact resolve eq18880 eq76351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18880 eq76351
  have eq76468 : y = (M.op y (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76370
       have i₂ := eq18700 x
       grind)
    | exact superpose eq18700 eq76370
    | exact resolve eq76370 eq18700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76370
  have eq76487 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq68859 eq76468
    | exact resolve eq76468 eq68859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68859 eq76468
  have eq76528 : (M.op x y) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = (M.op x y) ∨ (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq76487
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq76487
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq76487 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76487
  have eq76672 : (M.op x y) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq68877 eq76528
    | exact resolve eq76528 eq68877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76528
  have eq76695 : (M.op x y) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have r₁ := eq76672
       have r₂ := eq72014
       grind)
    | exact resolve eq76672 eq72014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76672
  have eq76703 : (M.op x y) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq68877 eq76695
    | exact resolve eq76695 eq68877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68877 eq76695
  have eq76704 : (M.op x y) = (M.op (M.op x y) (k x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq76703
  have eq76706 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq69257 eq76704
    | exact resolve eq76704 eq69257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69257 eq76704
  have eq76707 : x = (M.op x y) := by
    first
    | (have r₁ := eq76706
       have r₂ := eq72014
       grind)
    | exact resolve eq76706 eq72014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72014 eq76706
  have eq76709 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq76707
       grind)
    | exact superpose eq76707 eq22
    | exact resolve eq22 eq76707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq76711 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq76707
       grind)
    | exact superpose eq76707 eq39
    | exact resolve eq39 eq76707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq76769 : (M.op x y) = (k (M.op x y) (τ (M.op (σ y) (σ x)))) := by
    first
    | (have i₁ := eq14004
       have i₂ := eq76707
       grind)
    | exact superpose eq76707 eq14004
    | exact resolve eq14004 eq76707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14004
  have eq76955 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq76709 eq20
    | exact resolve eq20 eq76709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76709
  have eq77966 : (M.op x y) = (k (M.op x y) (τ (k (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76769
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq76769
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq76769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76769
  have eq77983 : (M.op x y) = (k (M.op x y) (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98 eq77966
    | exact resolve eq77966 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq77966
  have eq77992 : (M.op x y) = (k (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77983
       have i₂ := eq69517
       grind)
    | exact superpose eq69517 eq77983
    | exact resolve eq77983 eq69517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69517 eq77983
  have eq77996 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77992
       have i₂ := eq76707
       grind)
    | exact superpose eq76707 eq77992
    | exact resolve eq77992 eq76707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76707 eq77992
  have eq77997 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq77996
    | exact resolve eq77996 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77996
  have eq77998 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq77997
    | exact resolve eq77997 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77997
  have eq100805 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq68480 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq68480
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq68480
       grind)
    | exact resolve eq12 eq68480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68480
  have eq100873 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq100805
  have eq100892 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq100873
       have r₂ := eq26
       grind)
    | exact resolve eq100873 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100873
  have eq100909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq68459 eq100892
    | exact resolve eq100892 eq68459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68459 eq100892
  have eq100910 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq100909
  have eq100949 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq100910 eq13756
    | exact resolve eq13756 eq100910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100910
  have eq101112 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq100949
    | exact resolve eq100949 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100949
  have eq124341 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq77998 eq13756
    | exact resolve eq13756 eq77998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77998
  have eq124581 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq101112 eq124341
    | exact resolve eq124341 eq101112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124341
  have eq124715 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq124581
    | exact resolve eq124581 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124581
  have eq124716 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq124715
  have eq124805 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq124716 eq76711
    | exact resolve eq76711 eq124716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76711 eq124716
  have eq124814 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq124805
    | exact resolve eq124805 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq124805
  have eq124822 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76955 eq124814
    | exact resolve eq124814 eq76955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124814
  have eq127600 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq124822 eq984
    | (have j0 := eq984 (σ x)
       grind)
    | (have r₁ := eq984 (σ x)
       have r₂ := eq124822
       grind)
    | exact resolve eq984 eq124822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984 eq124822
  have eq127601 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq127600
  have eq127639 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op y (σ x))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127601 eq18881
    | exact resolve eq18881 eq127601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18881 eq127601
  have eq127767 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127639
       have i₂ := eq18700 sF2
       grind)
    | exact superpose eq18700 eq127639
    | exact resolve eq127639 eq18700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18700 eq127639
  have eq127790 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101112 eq127767
    | exact resolve eq127767 eq101112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127767
  have eq127844 : (σ y) = (M.op (σ y) (k (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127790
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq127790
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq127790 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127790
  have eq128039 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69497 eq127844
    | exact resolve eq127844 eq69497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69497 eq127844
  have eq128054 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq128039
    | exact resolve eq128039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128039
  have eq128061 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq128054
    | exact resolve eq128054 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128054
  have eq128062 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq128061
  have eq128064 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq101112 eq128062
    | exact resolve eq128062 eq101112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101112 eq128062
  have eq128065 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq128064
  have eq128103 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq128065 eq13756
    | exact resolve eq13756 eq128065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13756 eq128065
  have eq128309 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq128103
    | exact resolve eq128103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq128103
  have eq128310 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq128309
  have eq128372 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq128310 eq27
    | exact resolve eq27 eq128310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq128310
  have eq128658 : False := by grind
  exact eq128658

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxy_pyy_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
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
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq367 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq67
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op (M.op X3 X4) X0) X4)))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X2 X1 X0 (M.op (M.op (M.op X3 X4) X0) X4)
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op (M.op x y) X0) y)))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq462 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq437 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq437
    | exact resolve eq437 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq722 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op (M.op (M.op X2 X3) (σ X1)) X3))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (σ X1) (σ X0) X2 X3
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq53
    | (have j1 := eq69 X0 X1
       grind)
    | exact resolve eq53 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq5260 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 (M.op X0 X1) X2
       have i₂ := eq462 X2 X0 X1
       grind)
    | exact superpose eq462 eq67
    | exact resolve eq67 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq5261 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X1) X2
       have i₂ := eq462 X2 X0 X1
       grind)
    | exact superpose eq462 eq14
    | exact resolve eq14 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq5352 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq444 eq5260
    | exact resolve eq5260 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq5260
  have eq5570 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1 x (M.op X0 X1)
       have i₂ := eq5261 x (M.op X0 X1) X0
       grind)
    | exact superpose eq5261 eq367
    | exact resolve eq367 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq5571 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X0 X1)
       have i₂ := eq5261 x (M.op X0 X1) X0
       grind)
    | exact superpose eq5261 eq53
    | exact resolve eq53 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq5581 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq434 x sF0
       have i₂ := eq5261 x sF0 x
       grind)
    | exact superpose eq5261 eq434
    | exact resolve eq434 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq5594 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq435 x sF4
       have i₂ := eq5261 x sF4 sF2
       grind)
    | exact superpose eq5261 eq435
    | exact resolve eq435 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq5628 : y ≠ y ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5581 eq13
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq5581
       grind)
    | exact resolve eq13 eq5581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5652 : y = (k y (M.op x y)) := by grind
  clear eq5628
  have eq5777 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5594 eq13
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq5594
       grind)
    | exact resolve eq13 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5801 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5594 eq5352
    | exact resolve eq5352 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5352
  have eq5802 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq5777
  have eq5803 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq5594 eq5801
    | exact resolve eq5801 eq5594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5594 eq5801
  have eq5818 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq5652 eq90
    | exact resolve eq90 eq5652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5652
  have eq5830 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5818
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5818
    | exact resolve eq5818 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5818
  have eq6170 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 X2) (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443 X0 X2 X1 x (M.op X0 X1)
       have i₂ := eq5261 x (M.op X0 X1) X0
       grind)
    | exact superpose eq5261 eq443
    | exact resolve eq443 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq5261
  have eq7523 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5571 X0 (M.op X1 X0)
       have i₂ := eq5571 X1 X0
       grind)
    | exact superpose eq5571 eq5571
    | exact resolve eq5571 eq5571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24750 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (k (σ y) (σ (M.op x y))) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq90 eq722
    | (have j0 := eq722 y (M.op x y) x x
       grind)
    | exact resolve eq722 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq722
  have eq25123 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (k (σ y) (σ (M.op x y))) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq24750
    | (have j0 := eq24750 X0 X1
       grind)
    | exact resolve eq24750 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24750
  have eq25308 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq5830 eq25123
    | exact resolve eq25123 eq5830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5830 eq25123
  have eq25486 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq25308 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25308
    | (have j0 := eq25308 X0 X1
       grind)
    | exact resolve eq25308 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25308
  have eq25645 : ∀ X0 X1 : G, (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq25486
    | (have j0 := eq25486 X0 X1
       grind)
    | exact resolve eq25486 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25486
  have eq25761 : ∀ X0 X1 : G, (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq25645 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25645
    | (have j0 := eq25645 X0 X1
       grind)
    | exact resolve eq25645 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25645
  have eq25870 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq25761
    | (have j0 := eq25761 X0 X1
       grind)
    | exact resolve eq25761 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25761
  have eq25967 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq25870 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25870
    | (have j0 := eq25870 X0 X1
       grind)
    | exact resolve eq25870 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25870
  have eq49962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq49962
    | exact resolve eq49962 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49962
  have eq49981 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq49970
       have r₂ := eq28
       grind)
    | exact resolve eq49970 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49970
  have eq50048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq49981 eq5571
    | exact resolve eq5571 eq49981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49981
  have eq50079 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq50048
    | exact resolve eq50048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50048
  have eq50192 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq50079 eq5571
    | exact resolve eq5571 eq50079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50079
  have eq50219 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq50192
    | exact resolve eq50192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50192
  have eq50220 : y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq50219
  have eq50321 : y = (M.op x x) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5570 y x
       have i₂ := eq50220
       grind)
    | exact superpose eq50220 eq5570
    | exact resolve eq5570 eq50220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50322 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5571 y x
       have i₂ := eq50220
       grind)
    | exact superpose eq50220 eq5571
    | exact resolve eq5571 eq50220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50220
  have eq50353 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50322
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50322
    | exact resolve eq50322 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50322
  have eq50468 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5571 x x
       have i₂ := eq50353
       grind)
    | exact superpose eq50353 eq5571
    | exact resolve eq5571 eq50353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50353
  have eq50495 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50468
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq50468
    | exact resolve eq50468 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50468
  have eq50496 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq50495
  have eq50577 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50496 eq5802
    | exact resolve eq5802 eq50496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5802
  have eq50578 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50496 eq5803
    | exact resolve eq5803 eq50496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803 eq50496
  have eq50748 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq100 eq50577
    | exact resolve eq50577 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq50577
  have eq50785 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50578 eq58
    | exact resolve eq58 eq50578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq50578
  have eq50807 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq50785
    | exact resolve eq50785 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq50785
  have eq52480 : x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq50807
       grind)
    | exact superpose eq50807 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq50807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50807
  have eq52495 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52480
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52480
    | exact resolve eq52480 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52480
  have eq52496 : x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq52495
  have eq60623 : x = (k x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5570 x x
       have i₂ := eq50321
       grind)
    | exact superpose eq50321 eq5570
    | exact resolve eq5570 eq50321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5570 eq50321
  have eq60651 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60623
  have eq60689 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq60651
       grind)
    | exact superpose eq60651 eq45
    | exact resolve eq45 eq60651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq60651
  have eq60725 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq60689
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60689
    | exact resolve eq60689 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60689
  have eq60788 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60725 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq60725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60725
  have eq60796 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq60788
    | exact resolve eq60788 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60788
  have eq60797 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq60796
  have eq63124 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60797 eq7523
    | exact resolve eq7523 eq60797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60797
  have eq63146 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq63124
    | exact resolve eq63124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63124
  have eq63147 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63146
  have eq63268 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63147 eq5571
    | exact resolve eq5571 eq63147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68143 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7523 y y
       have i₂ := eq52496
       grind)
    | exact superpose eq52496 eq7523
    | exact resolve eq7523 eq52496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52496
  have eq68165 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68143
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68143
    | exact resolve eq68143 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68143
  have eq68166 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq68165
  have eq68273 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6170 X0 y x
       have i₂ := eq68166
       grind)
    | exact superpose eq68166 eq6170
    | exact resolve eq6170 eq68166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6170 eq68166
  have eq2586659 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5571 y x
       have i₂ := eq50748
       grind)
    | exact superpose eq50748 eq5571
    | exact resolve eq5571 eq50748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50748
  have eq2587702 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2586659
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2586659
    | exact resolve eq2586659 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586659
  have eq2587703 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2587702
  have eq2595642 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5571 x x
       have i₂ := eq2587703
       grind)
    | exact superpose eq2587703 eq5571
    | exact resolve eq5571 eq2587703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571 eq2587703
  have eq2596456 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2595642
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2595642
    | exact resolve eq2595642 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595642
  have eq2596457 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2596456
  have eq2596563 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2596457 eq30
    | exact resolve eq30 eq2596457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2596457
  have eq2598686 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2596563
    | exact resolve eq2596563 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2596563
  have eq2606081 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2598686 eq5581
    | exact resolve eq5581 eq2598686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581
  have eq2606649 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq2646304 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68273 y
       have i₂ := eq2606081
       grind)
    | exact superpose eq2606081 eq68273
    | exact resolve eq68273 eq2606081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68273 eq2606081
  have eq2647210 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2646304
  have eq2647654 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2647210
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2647210
    | exact resolve eq2647210 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647210
  have eq2821751 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2598686 eq2647654
    | exact resolve eq2647654 eq2598686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598686 eq2647654
  have eq2823406 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2821751
       have r₂ := eq2606649
       grind)
    | exact resolve eq2821751 eq2606649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606649 eq2821751
  have eq2823434 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2823406
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2823406
    | exact resolve eq2823406 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2823406
  have eq2823435 : x = (M.op x y) := by grind
  clear eq2823434
  have eq2823443 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2823435 eq21
    | exact resolve eq21 eq2823435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2823435
  have eq2824245 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2823443
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2823443
    | exact resolve eq2823443 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2823443
  have eq2824338 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2824245 eq27
    | exact resolve eq27 eq2824245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2824616 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2824245 eq63147
    | exact resolve eq63147 eq2824245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63147
  have eq2824629 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2824245 eq63268
    | exact resolve eq63268 eq2824245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63268 eq2824245
  have eq2826255 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2824629
       have r₂ := eq28
       grind)
    | exact resolve eq2824629 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824629
  have eq2826268 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2824616
       have r₂ := eq28
       grind)
    | exact resolve eq2824616 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824616
  have eq2834259 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2826268 eq25967
    | exact resolve eq25967 eq2826268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25967
  have eq2834420 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2834259
       have i₂ := eq7523 sF1 sF1
       grind)
    | exact superpose eq7523 eq2834259
    | exact resolve eq2834259 eq7523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7523 eq2834259
  have eq2834881 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2826255 eq2834420
    | exact resolve eq2834420 eq2826255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834420
  have eq2835031 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2826268 eq2834881
    | exact resolve eq2834881 eq2826268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834881
  have eq2835084 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2826268 eq2835031
    | exact resolve eq2835031 eq2826268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826268 eq2835031
  have eq2835085 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2835084
  have eq2835099 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2826255 eq2835085
    | exact resolve eq2835085 eq2826255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835085
  have eq2835100 : (σ (M.op x y)) = (σ y) := by grind
  clear eq2835099
  have eq2836377 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2835100 eq2824338
    | exact resolve eq2824338 eq2835100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824338 eq2835100
  have eq2836388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2826255 eq2836377
    | exact resolve eq2836377 eq2826255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826255 eq2836377
  have eq2836675 : False := by grind
  exact eq2836675

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
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
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq69 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq50
    | exact resolve eq50 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq73
  have eq99 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq101 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq99
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq122
    | exact resolve eq122 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq129
    | exact resolve eq129 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq221 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (σ (M.op x y)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq42
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq576 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq67
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op (M.op x y) X0) y)))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq666 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq666
    | exact resolve eq666 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq6336 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 (M.op X0 X1) X2
       have i₂ := eq695 X2 X0 X1
       grind)
    | exact superpose eq695 eq67
    | exact resolve eq67 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq6337 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X1) X2
       have i₂ := eq695 X2 X0 X1
       grind)
    | exact superpose eq695 eq14
    | exact resolve eq14 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq6434 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq674 eq6336
    | exact resolve eq6336 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq6336
  have eq6801 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 X1 x (M.op X0 X1)
       have i₂ := eq6337 x (M.op X0 X1) X0
       grind)
    | exact superpose eq6337 eq576
    | exact resolve eq576 eq6337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq6802 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X0 X1)
       have i₂ := eq6337 x (M.op X0 X1) X0
       grind)
    | exact superpose eq6337 eq53
    | exact resolve eq53 eq6337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6815 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq670 x sF0
       have i₂ := eq6337 x sF0 x
       grind)
    | exact superpose eq6337 eq670
    | exact resolve eq670 eq6337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq6828 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq671 x sF4
       have i₂ := eq6337 x sF4 sF2
       grind)
    | exact superpose eq6337 eq671
    | exact resolve eq671 eq6337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq6337
  have eq6863 : y ≠ y ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq6815 eq13
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq6815
       grind)
    | exact resolve eq13 eq6815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6815
  have eq6888 : y = (k y (M.op x y)) := by grind
  clear eq6863
  have eq6907 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq6828 eq14
    | exact resolve eq14 eq6828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6930 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq6828 eq6434
    | exact resolve eq6434 eq6828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6434
  have eq6932 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq6828 eq6930
    | exact resolve eq6930 eq6828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6828 eq6930
  have eq6948 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq6888 eq101
    | exact resolve eq101 eq6888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6960 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6948
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6948
    | exact resolve eq6948 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6948
  have eq10969 : (σ (k (k y (M.op x y)) (M.op x y))) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq101 eq221
    | exact resolve eq221 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq11035 : (M.op (σ (M.op x y)) (σ y)) = (σ (k (k y (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq6960 eq10969
    | exact resolve eq10969 eq6960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10969
  have eq11062 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq6888 eq11035
    | exact resolve eq11035 eq6888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6888 eq11035
  have eq11082 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq101 eq11062
    | exact resolve eq11062 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq11062
  have eq11099 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq6960 eq11082
    | exact resolve eq11082 eq6960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11082
  have eq11116 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq6960 eq11099
    | exact resolve eq11099 eq6960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11099
  have eq11128 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq6960 eq11116
    | exact resolve eq11116 eq6960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6960 eq11116
  have eq33761 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq130 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq33761
    | exact resolve eq33761 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33761
  have eq33780 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq33769
       have r₂ := eq28
       grind)
    | exact resolve eq33769 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33769
  have eq33792 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq33780 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq33780
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq33780
       grind)
    | exact resolve eq13 eq33780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33837 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq33780 eq6802
    | exact resolve eq6802 eq33780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33780
  have eq33869 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq33792
  have eq33874 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq33837
    | exact resolve eq33837 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33837
  have eq33963 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6801 y x
       have i₂ := eq33874
       grind)
    | exact superpose eq33874 eq6801
    | exact resolve eq6801 eq33874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq33964 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6802 y x
       have i₂ := eq33874
       grind)
    | exact superpose eq33874 eq6802
    | exact resolve eq6802 eq33874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33874
  have eq34001 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33964
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33964
    | exact resolve eq33964 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33964
  have eq34078 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq34001 eq6932
    | exact resolve eq6932 eq34001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6932 eq34001
  have eq35086 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq33963
       grind)
    | exact superpose eq33963 eq45
    | exact resolve eq45 eq33963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq33963
  have eq35116 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35086
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35086
    | exact resolve eq35086 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35086
  have eq35574 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq34078 eq58
    | exact resolve eq58 eq34078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq34078
  have eq35599 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq35574
    | exact resolve eq35574 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35574
  have eq35618 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35116 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq35116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35116
  have eq35626 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35618
  have eq35629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq35626
    | exact resolve eq35626 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35626
  have eq35630 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq35629
  have eq35766 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq35599
       grind)
    | exact superpose eq35599 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq35599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35599
  have eq35774 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq35766
  have eq35782 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35774
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35774
    | exact resolve eq35774 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35774
  have eq35783 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq35782
  have eq36650 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq33869 eq130
    | exact resolve eq130 eq33869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq33869
  have eq36666 : y = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq36650
  have eq36736 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6802 y x
       have i₂ := eq36666
       grind)
    | exact superpose eq36666 eq6802
    | exact resolve eq6802 eq36666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6802 eq36666
  have eq36775 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36736
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq36736
    | exact resolve eq36736 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36736
  have eq36816 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36775 eq30
    | exact resolve eq30 eq36775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36775
  have eq36948 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq36816
    | exact resolve eq36816 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36816
  have eq36949 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq36948
  have eq36980 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq36949 eq30
    | exact resolve eq30 eq36949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36949
  have eq37131 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq36980
    | exact resolve eq36980 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36980
  have eq37142 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) y)) = X0 ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37131 eq51
    | exact resolve eq51 eq37131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53036 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37142 x
       have i₂ := eq35783
       grind)
    | exact superpose eq35783 eq37142
    | exact resolve eq37142 eq35783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35783 eq37142
  have eq53257 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq53036
  have eq53365 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq53257
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53257
    | exact resolve eq53257 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53257
  have eq53400 : x = (M.op x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37131 eq53365
    | exact resolve eq53365 eq37131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37131 eq53365
  have eq53486 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq53400
  have eq53514 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53486
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53486
    | exact resolve eq53486 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53486
  have eq53515 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq53514
  have eq53518 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53515 eq30
    | exact resolve eq30 eq53515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53515
  have eq53729 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq53518
    | exact resolve eq53518 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq53518
  have eq53730 : x = (M.op x y) ∨ x = y := by grind
  clear eq53729
  have eq53760 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq53730 eq21
    | exact resolve eq21 eq53730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53936 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq53760
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53760
    | exact resolve eq53760 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53760
  have eq53989 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq53936 eq27
    | exact resolve eq27 eq53936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54061 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq53936 eq35630
    | exact resolve eq35630 eq53936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35630 eq53936
  have eq54094 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq54061
  have eq54107 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq54094
       have r₂ := eq28
       grind)
    | exact resolve eq54094 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54094
  have eq59693 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq54107 eq11128
    | exact resolve eq11128 eq54107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11128
  have eq59696 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq54107 eq6907
    | exact resolve eq6907 eq54107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6907 eq54107
  have eq59784 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq59693
  have eq60646 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59784 eq53989
    | exact resolve eq53989 eq59784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53989
  have eq60735 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq60646
  have eq119045 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq60735 eq59696
    | exact resolve eq59696 eq60735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59696 eq60735
  have eq119160 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq119045
  have eq135517 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59784 eq119160
    | exact resolve eq119160 eq59784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119160
  have eq135640 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq135517
  have eq135865 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq135640 eq59784
    | exact resolve eq59784 eq135640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59784 eq135640
  have eq135983 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq135865
  have eq136031 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq135983 eq30
    | exact resolve eq30 eq135983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq135983
  have eq136422 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq136031
    | exact resolve eq136031 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq136031
  have eq138735 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq136422 eq53730
    | exact resolve eq53730 eq136422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53730 eq136422
  have eq139054 : x = y := by grind
  clear eq138735
  have eq139217 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq139054
       grind)
    | exact superpose eq139054 eq19
    | exact resolve eq19 eq139054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq139218 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq139054
       grind)
    | exact superpose eq139054 eq25
    | exact resolve eq25 eq139054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq139054
  have eq139415 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq139218
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq139218
    | exact resolve eq139218 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq139218
  have eq139472 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq139415 eq27
    | exact resolve eq27 eq139415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq139415
  have eq140939 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq139472 eq74
    | exact resolve eq74 eq139472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq139472
  have eq141164 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq140939
       have i₂ := eq139217
       grind)
    | exact superpose eq139217 eq140939
    | exact resolve eq140939 eq139217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139217 eq140939
  have eq141188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq141164 eq15
    | exact resolve eq15 eq141164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141164
  have eq141296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq141188
    | exact resolve eq141188 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq141188
  have eq141319 : False := by grind
  exact eq141319

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pxx_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq18
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq284 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3))) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq297 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq293 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq293 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq293 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq298 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq284
    | (have j0 := eq284 X0 X1 x x
       grind)
    | exact resolve eq284 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq299 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq311 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq297 (σ X0)
       grind)
    | exact superpose eq297 eq15
    | exact resolve eq15 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq311 X0
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq311
    | exact resolve eq311 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq311
  have eq406 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3))) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq299 X1 X0
       grind)
    | exact superpose eq299 eq61
    | (have j1 := eq299 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3)) X1
       grind)
    | exact resolve eq61 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq299 (σ y) (σ x)
       grind)
    | exact superpose eq299 eq16
    | (have j1 := eq299 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq413
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq413
    | exact resolve eq413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq419 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq406
    | (have j0 := eq406 X0 X1 x x
       grind)
    | exact resolve eq406 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq425 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq419 X1 X0
       grind)
    | exact superpose eq419 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq419 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq419 X0 X1
       grind)
    | exact resolve eq12 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq587 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq438 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) X2
       have i₂ := eq76 X2 X0 X1
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq917 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 x (M.op X0 X1)
       have i₂ := eq862 x (M.op X0 X1) X0
       grind)
    | exact superpose eq862 eq61
    | exact resolve eq61 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq862
  have eq940 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq917 X0 (M.op X1 X0)
       have i₂ := eq917 X1 X0
       grind)
    | exact superpose eq917 eq917
    | exact resolve eq917 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq917 (σ X0) (σ X0)
       have i₂ := eq330 X0
       grind)
    | exact superpose eq330 eq917
    | exact resolve eq917 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op X2 X0)
       have i₂ := eq917 X2 X0
       grind)
    | exact superpose eq917 eq9
    | exact resolve eq9 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) X0
       have i₂ := eq917 X1 X0
       grind)
    | exact superpose eq917 eq12
    | (have j0 := eq12 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq917 X0 X1
       grind)
    | exact resolve eq12 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1002 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq940 X1 X0
       grind)
    | exact superpose eq940 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq940 X0 X1
       grind)
    | exact resolve eq12 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1002 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1017 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1014 X0 X1
       have i₂ := eq917 X0 X1
       grind)
    | exact superpose eq917 eq1014
    | exact resolve eq1014 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1026 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1017 X0 X1
       have i₂ := eq419 X1 X0
       grind)
    | exact superpose eq419 eq1017
    | (have j1 := eq419 X1 X0
       grind)
    | exact resolve eq1017 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1027 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1017 X0 X1
       have i₂ := eq299 X1 X0
       grind)
    | exact superpose eq299 eq1017
    | (have j1 := eq299 X1 X0
       grind)
    | exact resolve eq1017 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 (σ X0))
       have i₂ := eq1017 X1 (σ X0)
       grind)
    | exact superpose eq1017 eq28
    | exact resolve eq28 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1017
  have eq1052 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1045 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1045
    | exact resolve eq1045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1182 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X1 X0
       have i₂ := eq419 (σ X1) X0
       grind)
    | exact superpose eq419 eq1052
    | (have j1 := eq419 (σ X1) X0
       grind)
    | exact resolve eq1052 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X1 X0
       have i₂ := eq299 (σ X1) X0
       grind)
    | exact superpose eq299 eq1052
    | (have j1 := eq299 (σ X1) X0
       grind)
    | exact resolve eq1052 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq1052
  have eq1231 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) X1) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq945 X0
       grind)
    | exact superpose eq945 eq9
    | exact resolve eq9 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq1969 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1026 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2058 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1027 (τ X1) X0
       grind)
    | exact superpose eq1027 eq17
    | (have j1 := eq1027 (τ X1) X0
       grind)
    | exact resolve eq17 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1027
  have eq9166 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1182 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1182
    | (have j0 := eq1182 (σ X0) X1
       grind)
    | exact resolve eq1182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq9224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9166 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9166
    | (have j0 := eq9166 X0 X1
       grind)
    | exact resolve eq9166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9166
  have eq9483 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1183 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1183
    | (have j0 := eq1183 (σ X0) X1
       grind)
    | exact resolve eq1183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq9544 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9483 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9483
    | (have j0 := eq9483 X0 X1
       grind)
    | exact resolve eq9483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483
  have eq12100 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9224 x y
       grind)
    | exact superpose eq9224 eq16
    | (have j1 := eq9224 x y
       grind)
    | exact resolve eq16 eq9224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9224
  have eq12432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12100
       have i₂ := eq1026 x y
       grind)
    | exact superpose eq1026 eq12100
    | (have j1 := eq1026 x y
       grind)
    | exact resolve eq12100 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq12100
  have eq12437 : y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq12432
  have eq12443 : y = (k y x) := by
    first
    | (have j1 := eq1969 y x
       grind)
    | (have r₁ := eq12437
       have r₂ := eq1969 y x
       grind)
    | exact resolve eq12437 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969 eq12437
  have eq12459 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq438 x y
       have i₂ := eq12443
       grind)
    | exact superpose eq12443 eq438
    | exact resolve eq438 eq12443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12520 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq917 y x
       have i₂ := eq12459
       grind)
    | exact superpose eq12459 eq917
    | exact resolve eq917 eq12459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12459
  have eq12615 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq947 x y X0
       have i₂ := eq12520
       grind)
    | exact superpose eq12520 eq947
    | exact resolve eq947 eq12520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq14248 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 x))) ∨ (M.op x y) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq967 y x
       have i₂ := eq12615 X0
       grind)
    | exact superpose eq12615 eq967
    | (have j1 := eq12615 X0
       grind)
    | exact resolve eq967 eq12615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq12615
  have eq15200 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9544 y x
       grind)
    | exact superpose eq9544 eq16
    | (have j1 := eq9544 y x
       grind)
    | exact resolve eq16 eq9544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9544
  have eq15374 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq15200
       have i₂ := eq12443
       grind)
    | exact superpose eq12443 eq15200
    | exact resolve eq15200 eq12443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15200
  have eq15444 : (σ y) ≠ (σ y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15374
       have i₂ := eq12520
       grind)
    | exact superpose eq12520 eq15374
    | exact resolve eq15374 eq12520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12520
  have eq15456 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq15444
  have eq15479 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq438 y x
       have i₂ := eq15456
       grind)
    | exact superpose eq15456 eq438
    | exact resolve eq438 eq15456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq15456
  have eq15487 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq15479
  have eq25144 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2058 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2058
    | exact resolve eq2058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq25235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25144 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq25144
    | (have j0 := eq25144 X0 X1
       grind)
    | exact resolve eq25144 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25144
  have eq25354 : (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq25235 y x
       have i₂ := eq12443
       grind)
    | exact superpose eq12443 eq25235
    | (have j0 := eq25235 y x
       grind)
    | exact resolve eq25235 eq12443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25235
  have eq25470 : x = (k x y) := by
    first
    | (have r₁ := eq25354
       have r₂ := eq15374
       grind)
    | exact resolve eq25354 eq15374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15374 eq25354
  have eq46825 : y = (M.op y (M.op y x)) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14248 y
       have i₂ := eq15487
       grind)
    | exact superpose eq15487 eq14248
    | exact resolve eq14248 eq15487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14248
  have eq46978 : x = (M.op x y) ∨ y = (M.op y (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46825
       have i₂ := eq25470
       grind)
    | exact superpose eq25470 eq46825
    | exact resolve eq46825 eq25470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46825
  have eq46979 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) := by grind
  clear eq46978
  have eq47009 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46979
       have i₂ := eq15487
       grind)
    | exact superpose eq15487 eq46979
    | exact resolve eq46979 eq15487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15487 eq46979
  have eq47095 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq47009
  have eq47159 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq917 y x
       have i₂ := eq47095
       grind)
    | exact superpose eq47095 eq917
    | exact resolve eq917 eq47095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq47095
  have eq47202 : x = (M.op x y) := by grind
  clear eq47159
  have eq95011 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq418
       have i₂ := eq47202
       grind)
    | exact superpose eq47202 eq418
    | exact resolve eq418 eq47202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq95024 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
  clear eq95011
  have eq95050 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq95024
       have i₂ := eq25470
       grind)
    | exact superpose eq25470 eq95024
    | exact resolve eq95024 eq25470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25470 eq95024
  have eq95133 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq587 (σ y) (σ x)
       have i₂ := eq95050
       grind)
    | exact superpose eq95050 eq587
    | (have j0 := eq587 (σ y) (σ x)
       grind)
    | exact resolve eq587 eq95050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq95143 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq940 (σ x) (σ y)
       have i₂ := eq95050
       grind)
    | exact superpose eq95050 eq940
    | exact resolve eq940 eq95050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq95223 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq95143
       have i₂ := eq330 x
       grind)
    | exact superpose eq330 eq95143
    | exact resolve eq95143 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq95143
  have eq95227 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq419 (σ y) (σ x)
       grind)
    | (have r₁ := eq95133
       have r₂ := eq419 (σ y) (σ x)
       grind)
    | exact resolve eq95133 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq95133
  have eq95264 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq95227
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq95227
    | exact resolve eq95227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95227
  have eq95283 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95264
       have i₂ := eq12443
       grind)
    | exact superpose eq12443 eq95264
    | exact resolve eq95264 eq12443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12443 eq95264
  have eq95879 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95283
       grind)
    | exact superpose eq95283 eq16
    | exact resolve eq16 eq95283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95889 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq1231 x (σ y)
       have i₂ := eq95283
       grind)
    | exact superpose eq95283 eq1231
    | exact resolve eq1231 eq95283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq95283
  have eq96039 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq95889
       have i₂ := eq95223
       grind)
    | exact superpose eq95223 eq95889
    | exact resolve eq95889 eq95223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95223 eq95889
  have eq96043 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq95879
       have i₂ := eq47202
       grind)
    | exact superpose eq47202 eq95879
    | exact resolve eq95879 eq47202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47202 eq95879
  have eq96070 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq96039
       have i₂ := eq95050
       grind)
    | exact superpose eq95050 eq96039
    | exact resolve eq96039 eq95050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96039
  have eq96082 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq96070
       have i₂ := eq95050
       grind)
    | exact superpose eq95050 eq96070
    | exact resolve eq96070 eq95050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95050 eq96070
  have eq96092 : False := by grind
  exact eq96092
