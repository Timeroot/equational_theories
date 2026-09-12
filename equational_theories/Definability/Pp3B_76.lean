import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_pxx_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  clear eq18
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
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq291 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq292 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq291 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq291
    | (have j0 := eq291 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq291 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6219 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq6796 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq6798 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq292 X0 X1
       grind)
    | exact superpose eq292 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq292 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq292 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq292 X0 X0
       grind)
    | exact resolve eq13 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq6818 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6798 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6798
  have eq6819 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (k (τ (k X0 X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq6796 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6796
  have eq6828 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6818 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq6818 X0 X0
       have r₂ := eq13 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq6818 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | exact resolve eq6818 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6818
  have eq6829 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (k (k X0 X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6819 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq6819
    | (have j0 := eq6819 X0
       grind)
    | exact resolve eq6819 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6819
  have eq6840 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6828 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq6828
    | (have j0 := eq6828 X0 X1
       grind)
    | exact resolve eq6828 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6828
  have eq7196 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ (k X0 X0)))) = (τ (k (σ (k X0 X0)) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6829 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6829
    | (have j0 := eq6829 (σ X0)
       grind)
    | exact resolve eq6829 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6829
  have eq7256 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ (k X0 X0)))) = (k (τ (σ (k X0 X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7196 X0
       have i₂ := eq23 (σ (k X0 X0)) X0
       grind)
    | exact superpose eq23 eq7196
    | (have j0 := eq7196 X0
       grind)
    | exact resolve eq7196 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq7196
  have eq7277 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (τ (σ X0)) (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7256 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq7256
    | (have j0 := eq7256 X0
       grind)
    | exact resolve eq7256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7256
  have eq7293 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7277 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7277
    | (have j0 := eq7277 X0
       grind)
    | exact resolve eq7277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7277
  have eq7309 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7293 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7293
    | (have j0 := eq7293 X0
       grind)
    | exact resolve eq7293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7293
  have eq7367 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7309 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq7309
    | (have j0 := eq7309 (σ X0)
       grind)
    | exact resolve eq7309 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7309
  have eq7498 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7367 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq7367
    | (have j0 := eq7367 X0
       grind)
    | exact resolve eq7367 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7367
  have eq7620 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7498 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq7498
    | (have j0 := eq7498 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq7498 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7498
  have eq7713 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7620 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7620
  have eq7744 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq7713
  have eq11532 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6840 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6840
    | (have j0 := eq6840 (σ (k X0 X1)) (σ X0)
       grind)
    | exact resolve eq6840 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6840
  have eq11601 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11532 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11532
    | (have j0 := eq11532 X0 X1
       grind)
    | exact resolve eq11532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11532
  have eq11627 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11601 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11601
    | (have j0 := eq11601 X0 X1
       grind)
    | exact resolve eq11601 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11601
  have eq11648 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11627 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11627
    | (have j0 := eq11627 X0 X1
       grind)
    | exact resolve eq11627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11627
  have eq11668 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11648 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq11648
    | (have j0 := eq11648 X0 X1
       grind)
    | exact resolve eq11648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11648
  have eq11684 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11668 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11668
    | (have j0 := eq11668 X0 X1
       grind)
    | exact resolve eq11668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11668
  have eq11700 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11684 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11684
    | (have j0 := eq11684 X0 X1
       grind)
    | exact resolve eq11684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11684
  have eq29093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6218 x y
       grind)
    | exact superpose eq6218 eq16
    | (have j1 := eq6218 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6218 x y
       grind)
    | exact resolve eq16 eq6218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6218
  have eq29156 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq29093
  have eq29308 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29156
       grind)
    | exact superpose eq29156 eq16
    | exact resolve eq16 eq29156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29310 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq29156
       grind)
    | exact superpose eq29156 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq29156
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq29156
       grind)
    | exact resolve eq13 eq29156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29313 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64 (σ y) (σ x)
       have i₂ := eq29156
       grind)
    | exact superpose eq29156 eq64
    | exact resolve eq64 eq29156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29156
  have eq29346 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq29310
  have eq29347 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq29346
  have eq29349 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29347
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq29347
    | exact resolve eq29347 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29347
  have eq29350 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq29349
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq29349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29349
  have eq29353 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70 y
       have i₂ := eq29313
       grind)
    | exact superpose eq29313 eq70
    | exact resolve eq70 eq29313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29430 : (τ (M.op (σ y) (σ y))) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29353
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29353
    | exact resolve eq29353 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29353
  have eq29451 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29313 eq29430
    | exact resolve eq29430 eq29313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29313 eq29430
  have eq29465 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29451
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29451
    | exact resolve eq29451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29451
  have eq29509 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq29465
  have eq29566 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29509
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq29509
    | exact resolve eq29509 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29509
  have eq29594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq29566
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq29566 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29566
  have eq29614 : y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq29594
       have r₂ := eq16
       grind)
    | exact resolve eq29594 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29594
  have eq29641 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq291 y y
       have i₂ := eq29614
       grind)
    | exact superpose eq29614 eq291
    | (have j0 := eq291 y y
       grind)
    | exact resolve eq291 eq29614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29614
  have eq29662 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq29641
  have eq35874 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29662 eq29350
    | exact resolve eq29350 eq29662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29350 eq29662
  have eq35875 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq35874
       have r₂ := eq29308
       grind)
    | exact resolve eq35874 eq29308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29308 eq35874
  have eq35907 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq35875
  have eq35980 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35907
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq35907
    | exact resolve eq35907 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35907
  have eq36008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq35980
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq35980 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35980
  have eq36028 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq36008
       have r₂ := eq16
       grind)
    | exact resolve eq36008 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36008
  have eq36032 : y ≠ y ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq36028
       grind)
    | exact superpose eq36028 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq36028
       grind)
    | exact resolve eq13 eq36028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36035 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64 y x
       have i₂ := eq36028
       grind)
    | exact superpose eq36028 eq64
    | exact resolve eq64 eq36028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq36076 : y ≠ y ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq36032
  have eq36077 : y = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq36076
  have eq36231 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq36035 eq36077
    | exact resolve eq36077 eq36035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36035 eq36077
  have eq36234 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq291 y x
       have i₂ := eq36231
       grind)
    | exact superpose eq36231 eq291
    | (have j0 := eq291 y x
       grind)
    | exact resolve eq291 eq36231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq36250 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq36234
  have eq40440 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36250
       grind)
    | exact superpose eq36250 eq16
    | exact resolve eq16 eq36250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36250
  have eq40517 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq36028 eq40440
    | exact resolve eq40440 eq36028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40440
  have eq40518 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq40517
  have eq40575 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq40518
  have eq40642 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40575
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq40575
    | exact resolve eq40575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40575
  have eq40670 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq36231 eq40642
    | exact resolve eq40642 eq36231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36231 eq40642
  have eq40764 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40670
       grind)
    | exact superpose eq40670 eq16
    | exact resolve eq16 eq40670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40670
  have eq40833 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq36028 eq40764
    | exact resolve eq40764 eq36028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36028 eq40764
  have eq40834 : y = (M.op x x) := by grind
  clear eq40833
  have eq40860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7744 x
       have i₂ := eq40834
       grind)
    | exact superpose eq40834 eq7744
    | (have j0 := eq7744 x
       grind)
    | exact resolve eq7744 eq40834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7744
  have eq40908 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq40860
       have r₂ := eq16
       grind)
    | exact resolve eq40860 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40860
  have eq41215 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = y := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq40908
       grind)
    | exact superpose eq40908 eq70
    | exact resolve eq70 eq40908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq41307 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq41215
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41215
    | exact resolve eq41215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41215
  have eq41332 : (τ (σ x)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq40908 eq41307
    | exact resolve eq41307 eq40908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40908 eq41307
  have eq41347 : x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq41332
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41332
    | exact resolve eq41332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41332
  have eq41391 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11700 x x
       have i₂ := eq41347
       grind)
    | exact superpose eq41347 eq11700
    | (have j0 := eq11700 x x
       grind)
    | (have r₁ := eq11700 x x
       have r₂ := eq41347
       grind)
    | exact resolve eq11700 eq41347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11700 eq41347
  have eq41395 : x ≠ x ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq41391
  have eq41396 : x = (M.op x x) ∨ x = y := by grind
  clear eq41395
  have eq41422 : x = y ∨ x = y := by
    first
    | (have i₁ := eq41396
       have i₂ := eq40834
       grind)
    | exact superpose eq40834 eq41396
    | exact resolve eq41396 eq40834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41396
  have eq41423 : x = y := by grind
  clear eq41422
  have eq41453 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41423
       grind)
    | exact superpose eq41423 eq16
    | exact resolve eq16 eq41423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41454 : x = (M.op x x) := by
    first
    | (have i₁ := eq40834
       have i₂ := eq41423
       grind)
    | exact superpose eq41423 eq40834
    | exact resolve eq40834 eq41423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40834 eq41423
  have eq41464 : x = (M.op x x) := by grind
  clear eq41454
  have eq41466 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41453
       have i₂ := eq41464
       grind)
    | exact superpose eq41464 eq41453
    | exact resolve eq41453 eq41464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41453
  have eq41468 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6219 x
       have i₂ := eq41464
       grind)
    | exact superpose eq41464 eq6219
    | (have j0 := eq6219 x
       grind)
    | exact resolve eq6219 eq41464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6219
  have eq41514 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq41468
  have eq41530 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41514
       have i₂ := eq41464
       grind)
    | exact superpose eq41464 eq41514
    | exact resolve eq41514 eq41464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41464 eq41514
  have eq41531 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq41530
  have eq41542 : False := by grind
  exact eq41542

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4504 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  clear eq36
  have eq47 : ∀ X0 X1 : G, (σ (k (k y X0) X1)) = (k (k (σ y) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k y X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | exact resolve eq10 eq37
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
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
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq318 : ∀ X0 : G, (k (k (σ x) (σ y)) (σ X0)) = (σ (k (k x y) X0)) := by
    intro X0
    first
    | exact superpose eq99 eq35
    | exact resolve eq35 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq175 (τ X0)
       grind)
    | exact superpose eq175 eq35
    | exact resolve eq35 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq336 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq327 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq327
    | exact resolve eq327 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq427 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq500 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq355 (τ X0)
       grind)
    | exact superpose eq355 eq35
    | exact resolve eq35 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq519 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq500 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq500
    | exact resolve eq500 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq604 : ∀ X0 : G, (τ (k (k (σ x) (σ y)) X0)) = (k (k x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq99 eq427
    | exact resolve eq427 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq692 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | (have i₁ := eq16 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq692 x x X2 X3 X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq692
    | exact resolve eq692 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq701 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq700 x x X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq700
    | exact resolve eq700 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq702 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 (M.op x x)
       have i₂ := eq693 (M.op x x) x
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq693 x x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op x x) X2 X3
       have i₂ := eq693 (M.op x x) x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op x y) y) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq693 (M.op X0 X0) X0
       grind)
    | exact superpose eq693 eq28
    | (have j0 := eq28 X1 (M.op X0 X0)
       grind)
    | exact resolve eq28 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq720 eq701
    | exact resolve eq701 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq701 eq28
    | (have j0 := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq701 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq28 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq748 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq757 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq720 eq753
    | exact resolve eq753 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq764 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq757 eq35
    | exact resolve eq35 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq777 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq764 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq764
    | exact resolve eq764 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq803 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq701 x
       have i₂ := eq11 (M.op sF4 sF3) x
       grind)
    | exact superpose eq11 eq701
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f824_14 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
      intro X0
      grind
    have f824_18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
      intro X0 X1
      grind
    have f824_20 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
      intro X0 X1
      grind
    have f824_23 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
      intro X0 X1 X2 X3
      grind
    have f824_24 : (k (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (k (M.op (σ x) (σ y)) (σ y)) X0) := by grind
    have f824_25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
    have f824_92 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X3 X4) X4) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X0) = X0 := by
      intro X0 X1 X2 X3 X4
      first
      | (have i₁ := f824_23 X1 X2 X3 X4
         have i₂ := f824_18 X2 X0
         grind)
      | (have i₁ := f824_23 X0 X1 X2 X3
         have i₂ := f824_18 X0 (M.op X1 X1)
         grind)
      | exact superpose f824_18 f824_23
      | (have j1 := f824_18 X2 X0
         grind)
      | exact resolve f824_23 f824_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_93 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
      intro X0 X1
      grind
    have f824_1499 : (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
      first
      | (have i₁ := f824_24
         have i₂ := f824_93 (σ y) (M.op (σ x) (σ y))
         grind)
      | exact superpose f824_93 f824_24
      | (have j1 := f824_93 (σ y) (M.op (σ x) (σ y))
         grind)
      | exact resolve f824_24 f824_93
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_1558 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
      first
      | (have r₁ := f824_1499
         have r₂ := f824_14 X0
         grind)
      | exact resolve f824_1499 f824_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_1562 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
      first
      | (have r₁ := f824_1558
         have r₂ := f824_25
         grind)
      | exact resolve f824_1558 f824_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_3136 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op (M.op X1 X2) X2) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
      intro X0 X1 X2
      first
      | (have i₁ := f824_24
         have i₂ := f824_92 (σ y) X1 (M.op (σ x) (σ y)) x x
         grind)
      | exact superpose f824_92 f824_24
      | (have j1 := f824_92 (σ y) X0 X2 X1 X2
         grind)
      | exact resolve f824_24 f824_92
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_3210 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
      intro X0 X1 X2
      first
      | (have j0 := f824_3136 X0 X1 X2
         grind)
      | (have r₁ := f824_3136 X0 X1 X2
         have r₂ := f824_14 X0
         grind)
      | exact resolve f824_3136 f824_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_3231 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X0 (σ y)) := by
      intro X0 X1 X2
      first
      | (have j0 := f824_3210 X0 X1 X2
         grind)
      | (have r₁ := f824_3210 X0 X1 X2
         have r₂ := f824_25
         grind)
      | exact resolve f824_3210 f824_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_3267 : ∀ X0 X2 X3 : G, (M.op X3 (σ y)) = (M.op (M.op X0 (σ y)) X2) := by
      intro X0 X2 X3
      first
      | (have i₁ := f824_3231 X3 (M.op x X2) X2
         have i₂ := f824_3231 X0 x X2
         grind)
      | (have i₁ := f824_3231 X0 X0 (σ y)
         have i₂ := f824_3231 X0 x X2
         grind)
      | exact superpose f824_3231 f824_3231
      | exact resolve f824_3231 f824_3231
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_9593 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) X0) := by
      first
      | (have i₁ := f824_24
         have i₂ := f824_1562
         grind)
      | exact superpose f824_1562 f824_24
      | exact resolve f824_24 f824_1562
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f824_9600 : False := by
      first
      | (have r₁ := f824_9593
         have r₂ := f824_3267 (σ x) X0 (σ x)
         grind)
      | exact resolve f824_9593 f824_3267
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f824_9600
  clear eq701
  have eq827 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq839 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq803 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq854 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq810 X0
       have j1 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq810 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq810 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq810 x
       have r₂ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) x
       grind)
    | exact resolve eq810 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq856 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq808 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq808
    | (have j0 := eq808 X1 X1 x x
       grind)
    | exact resolve eq808 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq808
  have eq860 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq839 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq839 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq839 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq839 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq875 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq854 X0
       have j1 := eq28 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq854 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq854 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq877 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq720 eq856
    | (have j0 := eq856 X1 X1
       grind)
    | exact resolve eq856 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq886 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq720 eq875
    | exact resolve eq875 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq908 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq777 eq828
    | (have j0 := eq828 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq828 (σ (M.op (M.op x y) y))
       have r₂ := eq777 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq828 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op x y) y)))) := by
    intro X0
    first
    | exact superpose eq777 eq35
    | exact resolve eq35 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq921 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq908
  have eq931 : ∀ X0 : G, (k X0 (σ (σ (M.op (M.op x y) y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq911 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq911
    | exact resolve eq911 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq1114 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op x y) y))))) := by
    intro X0
    first
    | exact superpose eq931 eq35
    | exact resolve eq35 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq1134 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (M.op x y) y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1114 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1114
    | exact resolve eq1114 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1189 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq860 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq860
    | (have j0 := eq860 (σ X0) X1
       grind)
    | exact resolve eq860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq860 (τ X0) X1
       have i₂ := eq427 X0 X0
       grind)
    | exact superpose eq427 eq860
    | (have j0 := eq860 (τ X0) X1
       grind)
    | exact resolve eq860 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq1231 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (M.op x y) y)))))) := by
    intro X0
    first
    | exact superpose eq1134 eq35
    | exact resolve eq35 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1252 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (M.op (M.op x y) y)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1231 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1231
    | exact resolve eq1231 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1964 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op x y) y))))))) := by
    intro X0
    first
    | exact superpose eq1252 eq35
    | exact resolve eq35 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1967 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (σ (σ (σ (σ (M.op (M.op x y) y))))))) := by
    first
    | exact superpose eq1252 eq38
    | exact resolve eq38 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1252
  have eq1982 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (σ (σ (σ (σ (M.op (M.op x y) y))))))) := by
    first
    | exact superpose eq20 eq1967
    | exact resolve eq1967 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967
  have eq1985 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (M.op (M.op x y) y))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1964 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1964
    | exact resolve eq1964 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq2384 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq813
       grind)
    | exact superpose eq813 eq41
    | exact resolve eq41 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq2385 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2384
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2384
    | exact resolve eq2384 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384
  have eq2387 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2385
    | exact resolve eq2385 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2385
  have eq2441 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op x y) y)))))))) := by
    intro X0
    first
    | exact superpose eq1985 eq35
    | exact resolve eq35 eq1985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1985
  have eq2462 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op x y) y)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2441 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq2441
    | exact resolve eq2441 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq2623 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (k X1 (σ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1189 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1189
    | (have j0 := eq1189 (σ X0) X1
       grind)
    | exact resolve eq1189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4791 : (σ y) = (k (σ y) (σ (σ (σ (M.op (τ (τ y)) (τ (τ y))))))) := by
    first
    | (have i₁ := eq37 (σ (σ (M.op (τ (τ y)) (τ (τ y)))))
       have i₂ := eq519 y
       grind)
    | exact superpose eq519 eq37
    | exact resolve eq37 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq519
  have eq4843 : (σ y) = (k (σ y) (σ (σ (σ (M.op (τ (τ y)) (τ (τ y))))))) := by
    first
    | (have i₁ := eq4791
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4791
    | exact resolve eq4791 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4791
  have eq6435 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1) X1
       have i₂ := eq877 X0 X1
       grind)
    | exact superpose eq877 eq11
    | (have j0 := eq11 X1 X1
       have j1 := eq877 X1 X1
       grind)
    | exact resolve eq11 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6446 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq12089 : ∀ X0 : G, (σ (σ (σ (σ (σ (σ (σ (M.op (M.op x y) y)))))))) ≠ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op x y) y)))))))) ∨ (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op (M.op x y) y))))))))) = X0 := by
    intro X0
    first
    | exact superpose eq2462 eq1189
    | (have j0 := eq1189 (σ (σ (σ (σ (σ (σ (M.op (M.op x y) y))))))) X0
       grind)
    | exact resolve eq1189 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12148 : ∀ X0 : G, (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op (M.op x y) y))))))))) = X0 := by
    intro X0
    first
    | (have j0 := eq12089 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12089
  have eq19621 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq921 eq693
    | exact resolve eq693 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19640 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq921 eq707
    | exact resolve eq707 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq19643 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (σ (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq921 eq19640
    | exact resolve eq19640 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq19640
  have eq19656 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq702 eq19643
    | exact resolve eq19643 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19643
  have eq20761 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq19656 eq15
    | exact resolve eq15 eq19656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2387 eq821
    | exact resolve eq821 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23414 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23406
       have r₂ := eq27
       grind)
    | exact resolve eq23406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23406
  have eq23421 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23414 eq218
    | exact resolve eq218 eq23414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq23414
  have eq23459 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23421
    | exact resolve eq23421 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23421
  have eq23464 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq23459
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq23459
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq23459
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23459 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23459
  have eq23466 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23464 eq200
    | exact resolve eq200 eq23464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq23464
  have eq23506 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23466
    | exact resolve eq23466 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23466
  have eq23511 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq860 y x
       grind)
    | (have r₁ := eq23506
       have r₂ := eq860 y x
       grind)
    | exact resolve eq23506 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq23506
  have eq23512 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq23511
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23511 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23511
  have eq23518 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq23512
       grind)
    | exact superpose eq23512 eq41
    | exact resolve eq41 eq23512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq23519 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq877 x y
       have i₂ := eq23512
       grind)
    | exact superpose eq23512 eq877
    | (have j0 := eq877 y y
       grind)
    | exact resolve eq877 eq23512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23520 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23519
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23519
    | exact resolve eq23519 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23519
  have eq23521 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq23518
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23518
    | exact resolve eq23518 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23518
  have eq23528 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23521 eq2387
    | exact resolve eq2387 eq23521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq23531 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23521 eq821
    | exact resolve eq821 eq23521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq23535 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23521 eq877
    | (have j0 := eq877 (σ y) (σ y)
       grind)
    | exact resolve eq877 eq23521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq23536 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq23535
    | exact resolve eq23535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23535
  have eq23542 : (σ x) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23531 eq23536
    | exact resolve eq23536 eq23531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23536
  have eq23609 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23528
       grind)
    | exact superpose eq23528 eq706
    | exact resolve eq706 eq23528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23614 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23528 eq23609
    | exact resolve eq23609 eq23528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23528 eq23609
  have eq23653 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23531 eq706
    | exact resolve eq706 eq23531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23658 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq23531 eq23653
    | exact resolve eq23653 eq23531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23531 eq23653
  have eq24391 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq23614 eq19621
    | exact resolve eq19621 eq23614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24393 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23614 eq19656
    | exact resolve eq19656 eq23614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23614
  have eq24415 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24393
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24393
    | exact resolve eq24393 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24393
  have eq24417 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq24391 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24391
    | (have j0 := eq24391 X0
       grind)
    | exact resolve eq24391 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24391
  have eq24481 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24415 eq24417
    | exact resolve eq24417 eq24415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24417
  have eq24526 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq24415
       grind)
    | exact superpose eq24415 eq693
    | exact resolve eq693 eq24415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24415
  have eq29182 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24481 eq26
    | (have j1 := eq24481 (σ x)
       grind)
    | exact resolve eq26 eq24481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24481
  have eq29276 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq29182
       grind)
    | exact superpose eq29182 eq693
    | exact resolve eq693 eq29182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29293 : (M.op (M.op x y) y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq29182
       grind)
    | exact superpose eq29182 eq706
    | exact resolve eq706 eq29182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29652 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24526 x
       grind)
    | exact superpose eq24526 eq18
    | (have j1 := eq24526 x
       grind)
    | exact resolve eq18 eq24526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24526
  have eq29987 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq29652 eq19656
    | exact resolve eq19656 eq29652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29652
  have eq30013 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq29987
    | exact resolve eq29987 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29987
  have eq30346 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by grind
  have eq36292 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq29276 x
       grind)
    | exact superpose eq29276 eq18
    | (have j1 := eq29276 x
       grind)
    | exact resolve eq18 eq29276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29276
  have eq36646 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36292 eq19656
    | exact resolve eq19656 eq36292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36682 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq36646
    | exact resolve eq36646 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36646
  have eq36958 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36682 eq720
    | exact resolve eq720 eq36682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36965 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq30013 eq36958
    | exact resolve eq36958 eq30013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36958
  have eq43343 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) (σ y)) ∨ (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq36965 eq709
    | exact resolve eq709 eq36965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43368 : ∀ X0 : G, (M.op (M.op x y) (σ y)) ≠ (M.op (M.op x y) (σ y)) ∨ (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30013 eq43343
    | (have j0 := eq43343 X0
       grind)
    | exact resolve eq43343 eq30013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30013 eq43343
  have eq43369 : ∀ X0 : G, (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq43368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43368
  have eq43553 : ∀ X0 : G, (τ (M.op (M.op x y) (σ y))) ≠ (τ (M.op (M.op x y) (σ y))) ∨ (k X0 (τ (M.op (M.op x y) (σ y)))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq43369 eq1190
    | (have j0 := eq1190 (M.op (M.op x y) (σ y)) X0
       grind)
    | exact resolve eq1190 eq43369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43369
  have eq43595 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) (σ y)))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq43553 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43553
  have eq50095 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq318 y
       have i₂ := eq6446 x y
       grind)
    | exact superpose eq6446 eq318
    | (have j1 := eq6446 x y
       grind)
    | exact resolve eq318 eq6446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq50107 : (τ (M.op (M.op x y) y)) = (k (k x y) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604 sF3
       have i₂ := eq6446 sF2 sF3
       grind)
    | exact superpose eq6446 eq604
    | (have j1 := eq6446 (σ x) (σ y)
       grind)
    | exact resolve eq604 eq6446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq6446
  have eq50417 : (τ (M.op (M.op x y) y)) = (k (k x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq50107
    | exact resolve eq50107 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50107
  have eq50429 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq50095
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50095
    | exact resolve eq50095 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50095
  have eq50584 : (k x y) = (τ (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq50417
       have i₂ := eq23512
       grind)
    | exact superpose eq23512 eq50417
    | exact resolve eq50417 eq23512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50417
  have eq50596 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23521 eq50429
    | exact resolve eq50429 eq23521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50429
  have eq50640 : (k x y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20761 eq50584
    | exact resolve eq50584 eq20761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50584
  have eq50642 : (k (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19656 eq50596
    | exact resolve eq50596 eq19656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50596
  have eq50662 : x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq50640
       have i₂ := eq23512
       grind)
    | exact superpose eq23512 eq50640
    | exact resolve eq50640 eq23512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50640
  have eq50664 : (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23521 eq50642
    | exact resolve eq50642 eq23521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50642
  have eq50678 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23521 eq50662
    | exact resolve eq50662 eq23521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23521 eq50662
  have eq50679 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq50678
  have eq50680 : y = (M.op x x) ∨ (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq50664
       have i₂ := eq23512
       grind)
    | exact superpose eq23512 eq50664
    | exact resolve eq50664 eq23512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23512 eq50664
  have eq50681 : y = (M.op x x) ∨ (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) := by grind
  clear eq50680
  have eq50686 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23542 eq50679
    | exact resolve eq50679 eq23542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23542 eq50679
  have eq50687 : y = (M.op y y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23520 eq50681
    | exact resolve eq50681 eq23520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23520 eq50681
  have eq51036 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq50686 eq28
    | (have j0 := eq28 X0 (σ y)
       grind)
    | (have r₁ := eq28 X0 (σ y)
       have r₂ := eq50686
       grind)
    | exact resolve eq28 eq50686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51038 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq50686 eq693
    | exact resolve eq693 eq50686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51054 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50686 eq706
    | exact resolve eq706 eq50686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51056 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq51036 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51036
  have eq51059 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq50686 eq51054
    | exact resolve eq51054 eq50686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51054
  have eq51147 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq50687
       grind)
    | exact superpose eq50687 eq706
    | exact resolve eq706 eq50687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51152 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq50687 eq51147
    | exact resolve eq51147 eq50687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50687 eq51147
  have eq51215 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq51056 (M.op X1 X1)
       grind)
    | exact superpose eq51056 eq693
    | (have j1 := eq51056 X1
       grind)
    | exact resolve eq693 eq51056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51056
  have eq51556 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq51152 eq19621
    | exact resolve eq19621 eq51152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51558 : y = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq51152 eq19656
    | exact resolve eq19656 eq51152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51152
  have eq51624 : y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq51558
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51558
    | exact resolve eq51558 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51558
  have eq51626 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq51556 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51556
    | (have j0 := eq51556 X0
       grind)
    | exact resolve eq51556 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51556
  have eq51690 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq51624 eq51626
    | exact resolve eq51626 eq51624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51626
  have eq51774 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq51624
       grind)
    | exact superpose eq51624 eq693
    | exact resolve eq693 eq51624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52889 : y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51690 eq26
    | (have j1 := eq51690 (σ x)
       grind)
    | exact resolve eq26 eq51690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51690
  have eq52985 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq52889
       grind)
    | exact superpose eq52889 eq693
    | exact resolve eq693 eq52889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53002 : (M.op (M.op x y) y) = (M.op y x) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq52889
       grind)
    | exact superpose eq52889 eq706
    | exact resolve eq706 eq52889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53297 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq51774 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq51774 x
       grind)
    | exact superpose eq51774 eq18
    | (have j1 := eq51774 x
       grind)
    | exact resolve eq18 eq51774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51774
  have eq53610 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq53297 eq702
    | exact resolve eq702 eq53297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53691 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq53297 eq19656
    | exact resolve eq19656 eq53297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53770 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq53691
    | exact resolve eq53691 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53691
  have eq53842 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | (have r₁ := eq53770
       have r₂ := eq30346
       grind)
    | exact resolve eq53770 eq30346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30346 eq53770
  have eq53922 : (k (M.op x y) (M.op x y)) = (τ (k (M.op x y) (M.op x y))) ∨ y = (σ y) := by
    first
    | exact superpose eq53842 eq134
    | exact resolve eq134 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq58514 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq52985 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq52985 x
       grind)
    | exact superpose eq52985 eq18
    | (have j1 := eq52985 x
       grind)
    | exact resolve eq18 eq52985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58922 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58514 eq19656
    | exact resolve eq19656 eq58514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58932 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq58514 eq52985
    | exact resolve eq52985 eq58514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52985
  have eq58983 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq58932 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58932
  have eq59005 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq58922
    | exact resolve eq58922 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58922
  have eq59282 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq59005 eq720
    | exact resolve eq720 eq59005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59289 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq53842 eq59282
    | exact resolve eq59282 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59282
  have eq66199 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) (σ y)) ∨ (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq59289 eq709
    | exact resolve eq709 eq59289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq66226 : ∀ X0 : G, (M.op (M.op x y) (σ y)) ≠ (M.op (M.op x y) (σ y)) ∨ (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53842 eq66199
    | (have j0 := eq66199 X0
       grind)
    | exact resolve eq66199 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66199
  have eq66227 : ∀ X0 : G, (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq66226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66226
  have eq66288 : ∀ X0 : G, (τ (M.op (M.op x y) (σ y))) ≠ (τ (M.op (M.op x y) (σ y))) ∨ (k X0 (τ (M.op (M.op x y) (σ y)))) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq66227 eq1190
    | (have j0 := eq1190 (M.op (M.op x y) (σ y)) X0
       grind)
    | exact resolve eq1190 eq66227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66227
  have eq66339 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) (σ y)))) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq66288 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66288
  have eq76637 : ∀ X0 : G, (τ (τ (M.op (M.op x y) (σ y)))) ≠ (τ (τ (M.op (M.op x y) (σ y)))) ∨ (k X0 (τ (τ (M.op (M.op x y) (σ y))))) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq66339 eq1190
    | (have j0 := eq1190 (τ (M.op (M.op x y) (σ y))) X0
       grind)
    | exact resolve eq1190 eq66339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66339
  have eq76709 : ∀ X0 : G, (k X0 (τ (τ (M.op (M.op x y) (σ y))))) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq76637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76637
  have eq77124 : ∀ X0 : G, (τ (τ (M.op (M.op x y) (σ y)))) ≠ (τ (τ (M.op (M.op x y) (σ y)))) ∨ (k X0 (τ (τ (M.op (M.op x y) (σ y))))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq43595 eq1190
    | (have j0 := eq1190 (τ (M.op (M.op x y) (σ y))) X0
       grind)
    | exact resolve eq1190 eq43595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq43595
  have eq77196 : ∀ X0 : G, (k X0 (τ (τ (M.op (M.op x y) (σ y))))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq77124 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77124
  have eq77278 : ∀ X0 : G, (k X0 (τ (τ (M.op (M.op x y) (σ y))))) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq76709 eq77196
    | (have j0 := eq77196 X0
       have j1 := eq76709 X0
       grind)
    | exact resolve eq77196 eq76709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76709 eq77196
  have eq77279 : ∀ X0 : G, (k X0 (τ (τ (M.op (M.op x y) (σ y))))) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq77278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77278
  have eq77428 : ∀ X0 : G, (σ (σ (τ (τ (M.op (M.op x y) (σ y)))))) ≠ (σ (σ (τ (τ (M.op (M.op x y) (σ y)))))) ∨ (k X0 (σ (σ (τ (τ (M.op (M.op x y) (σ y))))))) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq77279 eq2623
    | (have j0 := eq2623 (τ (τ (M.op (M.op x y) (σ y)))) X0
       grind)
    | exact resolve eq2623 eq77279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623 eq77279
  have eq77498 : ∀ X0 : G, (k X0 (σ (σ (τ (τ (M.op (M.op x y) (σ y))))))) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq77428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77428
  have eq77558 : ∀ X0 : G, (k X0 (σ (τ (M.op (M.op x y) (σ y))))) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq77498 X0
       have i₂ := eq14 (τ (M.op sF0 sF3))
       grind)
    | exact superpose eq14 eq77498
    | exact resolve eq77498 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77498
  have eq77594 : ∀ X0 : G, (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq77558 X0
       have i₂ := eq14 (M.op sF0 sF3)
       grind)
    | exact superpose eq14 eq77558
    | exact resolve eq77558 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77558
  have eq77627 : (M.op (M.op x y) (σ y)) ≠ (M.op (M.op x y) (σ y)) ∨ (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq77594 eq828
    | (have j0 := eq828 (M.op (M.op x y) (σ y))
       grind)
    | (have r₁ := eq828 (M.op (M.op x y) (σ y))
       have r₂ := eq77594 (M.op (M.op x y) (σ y))
       grind)
    | exact resolve eq828 eq77594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77633 : ∀ X0 : G, (σ (M.op (M.op x y) (σ y))) ≠ (σ (M.op (M.op x y) (σ y))) ∨ (k X0 (σ (M.op (M.op x y) (σ y)))) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq77594 eq1189
    | (have j0 := eq1189 (M.op (M.op x y) (σ y)) X0
       grind)
    | exact resolve eq1189 eq77594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq77691 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) (σ y)))) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq77633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77633
  have eq77694 : (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq77627
  have eq78100 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (k y (M.op (M.op x y) (σ y))) X0)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq77691 eq47
    | exact resolve eq47 eq77691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq77691
  have eq78124 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (k (σ y) (M.op (M.op x y) (σ y))) X0)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53842 eq78100
    | exact resolve eq78100 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78100
  have eq78208 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (σ y) X0)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq77594 eq78124
    | exact resolve eq78124 eq77594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77594 eq78124
  have eq78700 : (σ (σ y)) = (k (σ y) (σ (σ (σ (σ (M.op (τ (τ y)) (τ (τ y)))))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq4843 eq78208
    | exact resolve eq78208 eq4843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4843
  have eq78745 : (σ (σ y)) = (k (σ y) (σ (σ (σ (σ (σ (σ (σ (M.op (M.op x y) y))))))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2462 eq78208
    | exact resolve eq78208 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq78801 : ∀ X0 : G, (k (σ y) (σ (τ X0))) = (k (σ (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq78208 eq39
    | exact resolve eq39 eq78208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq78208
  have eq79016 : ∀ X0 : G, (k (σ y) X0) = (k (σ (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq78801 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq78801
    | exact resolve eq78801 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78801
  have eq79057 : (σ y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12148 eq78745
    | exact resolve eq78745 eq12148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12148 eq78745
  have eq79093 : (σ (σ y)) = (k (σ y) (σ (σ (σ (σ (M.op (τ (τ (σ y))) (τ (τ (σ y))))))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq53842 eq78700
    | exact resolve eq78700 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78700
  have eq79196 : (σ (σ y)) = (k (σ y) (σ (σ (σ (σ (M.op (τ y) (τ y))))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32 eq79093
    | exact resolve eq79093 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79093
  have eq79211 : (σ (σ y)) = (k (σ y) (σ (σ (σ (σ (M.op (τ (σ y)) (τ (σ y)))))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq53842 eq79196
    | exact resolve eq79196 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79196
  have eq79219 : (σ (σ y)) = (k (σ y) (σ (σ (σ (σ (M.op y y)))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq32 eq79211
    | exact resolve eq79211 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79211
  have eq79222 : (σ (σ y)) = (k (σ y) (σ (σ (σ (σ (M.op (σ y) (σ y))))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq53842 eq79219
    | exact resolve eq79219 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79219
  have eq79223 : (σ y) = (k (σ y) (σ (σ (σ (σ (M.op (σ y) (σ y))))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq79057 eq79222
    | exact resolve eq79222 eq79057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79057 eq79222
  have eq83637 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq77694 eq693
    | exact resolve eq693 eq77694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77694
  have eq83675 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op X0 (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53842 eq83637
    | exact resolve eq83637 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83637
  have eq85645 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq51038 eq26
    | (have j1 := eq51038 (σ x)
       grind)
    | exact resolve eq26 eq51038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51038
  have eq85685 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51059 eq85645
    | exact resolve eq85645 eq51059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51059 eq85645
  have eq86022 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq85685 eq693
    | exact resolve eq693 eq85685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85685
  have eq86357 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86022 eq26
    | (have j1 := eq86022 (σ x)
       grind)
    | exact resolve eq26 eq86022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86832 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq86357 eq739
    | exact resolve eq739 eq86357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86928 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq86357 eq86022
    | exact resolve eq86022 eq86357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86978 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86357 eq58983
    | exact resolve eq58983 eq86357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58983 eq86357
  have eq86997 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq86978
  have eq87021 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq86928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86928
  have eq101158 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq51215 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq51215 eq26
    | (have j1 := eq51215 (σ x) X0
       grind)
    | exact resolve eq26 eq51215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101644 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ x = (σ x) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0
       have i₂ := eq101158 (M.op sF0 y)
       grind)
    | exact superpose eq101158 eq886
    | (have j1 := eq101158 X1
       grind)
    | exact resolve eq886 eq101158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq101708 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq19656
       have i₂ := eq101158 (M.op sF0 y)
       grind)
    | exact superpose eq101158 eq19656
    | (have j1 := eq101158 X0
       grind)
    | exact resolve eq19656 eq101158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101709 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq20761
       have i₂ := eq101158 (M.op sF0 y)
       grind)
    | exact superpose eq101158 eq20761
    | (have j1 := eq101158 X0
       grind)
    | exact resolve eq20761 eq101158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101158
  have eq102243 : (τ (σ y)) = (k y (τ (σ y))) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq101708 eq108
    | exact resolve eq108 eq101708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq101708
  have eq102257 : y = (k y y) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32 eq102243
    | exact resolve eq102243 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102243
  have eq102388 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq101709 eq828
    | (have j0 := eq828 (σ y)
       grind)
    | (have r₁ := eq828 (σ y)
       have r₂ := eq101709 (σ y)
       grind)
    | exact resolve eq828 eq101709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101709
  have eq102490 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq102388
  have eq102767 : y ≠ y ∨ y = (M.op y y) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq828 y
       have i₂ := eq102257
       grind)
    | exact superpose eq102257 eq828
    | (have j0 := eq828 y
       grind)
    | (have r₁ := eq828 y
       have r₂ := eq102257
       grind)
    | exact resolve eq828 eq102257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102257
  have eq102792 : y = (M.op y y) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by grind
  clear eq102767
  have eq103047 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq102490 eq693
    | exact resolve eq693 eq102490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq102490
  have eq103100 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (σ y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq86022 eq103047
    | (have j0 := eq103047 X0
       have j1 := eq86022 X0
       grind)
    | exact resolve eq103047 eq86022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86022 eq103047
  have eq103128 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ y = (σ y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq32 eq103100
    | (have j0 := eq103100 X0
       grind)
    | exact resolve eq103100 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103100
  have eq103513 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq102792
       grind)
    | exact superpose eq102792 eq706
    | exact resolve eq706 eq102792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103518 : y = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq102792 eq103513
    | exact resolve eq103513 eq102792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102792 eq103513
  have eq103884 : y = (σ y) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq103518 eq19656
    | exact resolve eq19656 eq103518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103518
  have eq104011 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq103884
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq103884
    | exact resolve eq103884 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103884
  have eq104169 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq104011 eq15
    | exact resolve eq15 eq104011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104011
  have eq104363 : (σ y) = (τ (σ y)) ∨ x = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq86997 eq104169
    | exact resolve eq104169 eq86997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86997 eq104169
  have eq104407 : (σ y) = (τ (σ y)) ∨ x = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq104363
  have eq104420 : y = (σ y) ∨ x = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq104407
    | exact resolve eq104407 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104407
  have eq104421 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by grind
  clear eq104420
  have eq109325 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq104421 eq27
    | exact resolve eq27 eq104421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104421
  have eq109394 : (M.op x y) = (σ x) ∨ x = (σ x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq109325
       have r₂ := eq53842
       grind)
    | exact resolve eq109325 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109325
  have eq112439 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have j0 := eq101644 (σ y) (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101644
  have eq112440 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (σ x) := by grind
  clear eq112439
  have eq112521 : (σ y) = (k (σ y) (σ y)) ∨ x = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36682 eq112440
    | exact resolve eq112440 eq36682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36682
  have eq112522 : (σ y) = (k (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq59005 eq112440
    | exact resolve eq112440 eq59005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112528 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq112440 eq824
    | exact resolve eq824 eq112440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq112440
  have eq112542 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq86832 eq112528
    | (have j0 := eq112528 X0
       have j1 := eq86832 X0
       grind)
    | exact resolve eq112528 eq86832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86832 eq112528
  have eq112543 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq112542 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112542
  have eq112544 : (σ y) = (k (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq112522 eq112521
    | exact resolve eq112521 eq112522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112521 eq112522
  have eq112545 : (σ y) = (k (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq112544
  have eq112623 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq112545 eq828
    | (have j0 := eq828 (σ y)
       grind)
    | (have r₁ := eq828 (σ y)
       have r₂ := eq112545
       grind)
    | exact resolve eq828 eq112545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112545
  have eq112648 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq112623
  have eq113058 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq112648 eq36965
    | exact resolve eq36965 eq112648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36965
  have eq113059 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq112648 eq59289
    | exact resolve eq59289 eq112648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59289 eq112648
  have eq113125 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq113059
  have eq113126 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq113058
  have eq113169 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq113125 eq113126
    | exact resolve eq113126 eq113125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113125 eq113126
  have eq113170 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq113169
  have eq113260 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq113170 eq83675
    | exact resolve eq83675 eq113170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83675 eq113170
  have eq113305 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq113260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113260
  have eq117293 : ∀ X0 : G, (M.op X0 (σ y)) = (τ (M.op X0 (σ y))) ∨ y = (σ y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq103128 eq20761
    | exact resolve eq20761 eq103128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20761 eq103128
  have eq121521 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq112543 eq19621
    | exact resolve eq19621 eq112543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19621 eq112543
  have eq123902 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (k X1 (σ y)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq121521 eq51215
    | (have j0 := eq51215 X0 X1
       grind)
    | exact resolve eq51215 eq121521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51215 eq121521
  have eq123989 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (k X1 (σ y)) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq123902 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123902
  have eq124032 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq123989 X0 X1
       have j1 := eq28 X1 (σ y)
       grind)
    | (have r₁ := eq123989 X0 X1
       have r₂ := eq28 X0 (σ y)
       grind)
    | exact resolve eq123989 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq123989
  have eq143686 : (σ y) = (τ (σ y)) ∨ y = (σ y) ∨ x = (σ x) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50686 eq117293
    | exact resolve eq117293 eq50686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50686 eq117293
  have eq143787 : (σ y) = (τ (σ y)) ∨ y = (σ y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq143686
  have eq143856 : y = (σ y) ∨ y = (σ y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq143787
    | exact resolve eq143787 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143787
  have eq143857 : y = (σ y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq143856
  have eq143902 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq109394 eq143857
    | exact resolve eq143857 eq109394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143857
  have eq144000 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq143902 eq11
    | exact resolve eq11 eq143902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144013 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ y = (σ y) := by grind
  clear eq144000
  have eq152387 : (σ y) = (τ (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq144013 eq53922
    | exact resolve eq53922 eq144013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53922 eq144013
  have eq152456 : (σ y) = (τ (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by grind
  clear eq152387
  have eq152495 : y = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq32 eq152456
    | exact resolve eq152456 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152456
  have eq152496 : (M.op x y) = (σ y) ∨ y = (σ y) ∨ x = (σ x) := by grind
  clear eq152495
  have eq152513 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq152496 eq26
    | exact resolve eq26 eq152496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153058 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq109394 eq152513
    | exact resolve eq152513 eq109394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109394 eq152513
  have eq153136 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq143902 eq153058
    | exact resolve eq153058 eq143902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143902 eq153058
  have eq153174 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq152496 eq153136
    | exact resolve eq153136 eq152496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152496 eq153136
  have eq153750 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq153174 eq27
    | exact resolve eq27 eq153174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153948 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have r₁ := eq153750
       have r₂ := eq53842
       grind)
    | exact resolve eq153750 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153750
  have eq153963 : (M.op x y) = (M.op x (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq153948
       grind)
    | exact superpose eq153948 eq18
    | exact resolve eq18 eq153948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153964 : (σ y) = (σ (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24
       have i₂ := eq153948
       grind)
    | exact superpose eq153948 eq24
    | exact resolve eq24 eq153948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153986 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op X0 (M.op (M.op x y) (σ y))) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq702 X0
       have i₂ := eq153948
       grind)
    | exact superpose eq153948 eq702
    | exact resolve eq702 eq153948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq153948
  have eq154911 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq153963 eq87021
    | exact resolve eq87021 eq153963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87021
  have eq154919 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq153963 eq113305
    | exact resolve eq113305 eq153963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113305
  have eq154927 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (k X0 (σ y)) = X0 ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq153963 eq124032
    | (have j0 := eq124032 X0 X0
       grind)
    | exact resolve eq124032 eq153963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124032
  have eq154951 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq154927 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154927
  have eq154959 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq154919
  have eq154967 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq154911
  have eq155068 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq154967 eq720
    | exact resolve eq720 eq154967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155148 : (M.op x y) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq154967
  have eq155233 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153174 eq155068
    | exact resolve eq155068 eq153174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153174 eq155068
  have eq156647 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq154959 eq153964
    | exact resolve eq153964 eq154959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153964 eq154959
  have eq156653 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq156647
  have eq156822 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq156653
    | exact resolve eq156653 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156653
  have eq156823 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by grind
  clear eq156822
  have eq159616 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq154951 eq828
    | (have j0 := eq828 (σ y)
       grind)
    | (have r₁ := eq828 (σ y)
       have r₂ := eq154951 (σ y)
       grind)
    | exact resolve eq828 eq154951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq154951
  have eq159726 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq159616
  have eq169519 : (σ y) = (M.op (M.op x y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq155233 eq159726
    | exact resolve eq159726 eq155233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155233 eq159726
  have eq169621 : (σ y) = (M.op (M.op x y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq169519
  have eq169770 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq169621 eq153986
    | exact resolve eq153986 eq169621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153986 eq169621
  have eq169859 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq169770 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169770
  have eq172049 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq169859 eq153963
    | exact resolve eq153963 eq169859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153963 eq169859
  have eq172175 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq172049
  have eq172269 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have r₁ := eq172175
       have r₂ := eq155148
       grind)
    | exact resolve eq172175 eq155148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155148 eq172175
  have eq172325 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq172269 eq27
    | exact resolve eq27 eq172269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172269
  have eq172520 : x = (σ x) := by
    first
    | (have r₁ := eq172325
       have r₂ := eq156823
       grind)
    | exact resolve eq172325 eq156823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156823 eq172325
  have eq172528 : (M.op x y) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq172520
       grind)
    | exact superpose eq172520 eq18
    | exact resolve eq18 eq172520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq172582 : y = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29182
       have i₂ := eq172520
       grind)
    | exact superpose eq172520 eq29182
    | exact resolve eq29182 eq172520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29182
  have eq172583 : (M.op (M.op x y) y) = (M.op y (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29293
       have i₂ := eq172520
       grind)
    | exact superpose eq172520 eq29293
    | exact resolve eq29293 eq172520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29293
  have eq172592 : y = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq51624
       have i₂ := eq172520
       grind)
    | exact superpose eq172520 eq51624
    | exact resolve eq51624 eq172520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51624
  have eq172597 : y = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52889
       have i₂ := eq172520
       grind)
    | exact superpose eq172520 eq52889
    | exact resolve eq52889 eq172520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52889
  have eq172598 : (M.op (M.op x y) y) = (M.op y (σ x)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53002
       have i₂ := eq172520
       grind)
    | exact superpose eq172520 eq53002
    | exact resolve eq53002 eq172520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53002 eq172520
  have eq172632 : (M.op x y) = (M.op y (σ x)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58514 eq172598
    | exact resolve eq172598 eq58514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58514 eq172598
  have eq172640 : (M.op x y) = (M.op y (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36292 eq172583
    | exact resolve eq172583 eq36292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36292 eq172583
  have eq172641 : y = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172597 eq172582
    | exact resolve eq172582 eq172597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172582 eq172597
  have eq172660 : (M.op x y) = (M.op y (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172632 eq172640
    | exact resolve eq172640 eq172632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172632 eq172640
  have eq172661 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53842 eq172641
    | exact resolve eq172641 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172641
  have eq172671 : (M.op x y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53842 eq172660
    | exact resolve eq172660 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172660
  have eq172672 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59005 eq172661
    | exact resolve eq172661 eq59005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172661
  have eq172675 : (M.op x y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59005 eq172671
    | exact resolve eq172671 eq59005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59005 eq172671
  have eq179062 : y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq172592 eq23658
    | exact resolve eq23658 eq172592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23658 eq172592
  have eq179118 : y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) := by grind
  clear eq179062
  have eq179156 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq53297 eq179118
    | exact resolve eq179118 eq53297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179118
  have eq179463 : (M.op (M.op x y) y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172672 eq706
    | exact resolve eq706 eq172672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179495 : (M.op (M.op x y) (σ y)) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53842 eq179463
    | exact resolve eq179463 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179463
  have eq179515 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172675 eq179495
    | exact resolve eq179495 eq172675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179495
  have eq179569 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172675 eq706
    | exact resolve eq706 eq172675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq172675
  have eq179583 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53842 eq179569
    | exact resolve eq179569 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179569
  have eq179591 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172672 eq179583
    | exact resolve eq179583 eq172672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172672 eq179583
  have eq179596 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq179515 eq179591
    | exact resolve eq179591 eq179515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179515 eq179591
  have eq181115 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq179156 eq720
    | exact resolve eq720 eq179156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq181273 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq26 eq181115
    | exact resolve eq181115 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181115
  have eq181286 : (σ x) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq179156 eq181273
    | exact resolve eq181273 eq179156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179156 eq181273
  have eq181289 : (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq53297 eq181286
    | exact resolve eq181286 eq53297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53297 eq181286
  have eq181290 : (M.op x y) = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq181289
  have eq181291 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq181290 eq26
    | exact resolve eq26 eq181290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181290
  have eq181771 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq53610 eq181291
    | exact resolve eq181291 eq53610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53610 eq181291
  have eq183429 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq181771 eq27
    | exact resolve eq27 eq181771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181771
  have eq183557 : (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq183429
       have r₂ := eq53842
       grind)
    | exact resolve eq183429 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183429
  have eq183559 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq183557 eq26
    | exact resolve eq26 eq183557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183692 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | exact superpose eq183557 eq172528
    | exact resolve eq172528 eq183557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183557
  have eq184196 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq183692 eq739
    | exact resolve eq739 eq183692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq183692
  have eq185110 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq184196 eq183559
    | exact resolve eq183559 eq184196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183559 eq184196
  have eq185257 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq185110
  have eq185640 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq185257 eq27
    | exact resolve eq27 eq185257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185257
  have eq185765 : y = (σ y) := by
    first
    | (have r₁ := eq185640
       have r₂ := eq53842
       grind)
    | exact resolve eq185640 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53842 eq185640
  have eq185772 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq185765
       grind)
    | exact superpose eq185765 eq24
    | exact resolve eq24 eq185765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq185996 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq172528
       have i₂ := eq185765
       grind)
    | exact superpose eq185765 eq172528
    | exact resolve eq172528 eq185765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172528 eq185765
  have eq186404 : (σ y) = (τ (σ y)) := by
    first
    | exact superpose eq185772 eq15
    | exact resolve eq15 eq185772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185772
  have eq187003 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq185996 eq26
    | exact resolve eq26 eq185996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq185996
  have eq187080 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq187003 eq27
    | exact resolve eq27 eq187003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq187176 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq187003 eq179596
    | exact resolve eq179596 eq187003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179596 eq187003
  have eq187177 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq187176
  have eq187195 : y = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq187177 eq32
    | exact resolve eq32 eq187177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq187372 : ∀ X0 : G, (k (M.op x y) X0) = (k (σ (M.op x y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq187177 eq79016
    | exact resolve eq79016 eq187177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79016
  have eq187377 : (M.op x y) = (k (M.op x y) (σ (σ (σ (σ (M.op (M.op x y) (M.op x y))))))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq187177 eq79223
    | exact resolve eq79223 eq187177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79223
  have eq187566 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq187177 eq186404
    | exact resolve eq186404 eq187177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186404 eq187177
  have eq187605 : (M.op x y) = (k (M.op x y) (σ (σ (σ (σ (M.op (M.op x y) (M.op x y))))))) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq187377
  have eq187610 : ∀ X0 : G, (k (M.op x y) X0) = (k (σ (M.op x y)) X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq187372 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187372
  have eq187657 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have r₁ := eq187566
       have r₂ := eq187080
       grind)
    | exact resolve eq187566 eq187080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187566
  have eq187713 : (M.op x y) = (k (M.op x y) (σ (σ (σ (σ (M.op (M.op x y) (M.op x y))))))) := by
    first
    | (have r₁ := eq187605
       have r₂ := eq187080
       grind)
    | exact resolve eq187605 eq187080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187605
  have eq187718 : ∀ X0 : G, (k (M.op x y) X0) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq187610 X0
       grind)
    | (have r₁ := eq187610 X0
       have r₂ := eq187080
       grind)
    | exact resolve eq187610 eq187080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187610
  have eq187877 : y = (τ (M.op x y)) := by
    first
    | (have r₁ := eq187195
       have r₂ := eq187080
       grind)
    | exact resolve eq187195 eq187080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187195
  have eq187912 : ∀ X0 : G, (k (M.op x y) X0) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq187718
    | (have j0 := eq187718 X0
       grind)
    | exact resolve eq187718 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq187718
  have eq188037 : y = (M.op x y) := by
    first
    | exact superpose eq187657 eq187877
    | exact resolve eq187877 eq187657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187657 eq187877
  have eq188390 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (σ (σ (σ (σ (M.op (M.op x y) (M.op x y)))))))) := by
    first
    | (have i₁ := eq1982
       have i₂ := eq188037
       grind)
    | exact superpose eq188037 eq1982
    | exact resolve eq1982 eq188037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq188414 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq19656
       have i₂ := eq188037
       grind)
    | exact superpose eq188037 eq19656
    | exact resolve eq19656 eq188037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19656 eq188037
  have eq188681 : (σ (M.op x y)) = (k (M.op x y) (σ (σ (σ (σ (σ (M.op (M.op x y) (M.op x y)))))))) := by
    first
    | exact superpose eq187912 eq188390
    | exact resolve eq188390 eq187912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187912 eq188390
  have eq188772 : (σ (M.op x y)) = (k (M.op x y) (σ (σ (σ (σ (M.op (M.op x y) (M.op x y))))))) := by
    first
    | exact superpose eq188414 eq188681
    | exact resolve eq188681 eq188414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188414 eq188681
  have eq188818 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq187713 eq188772
    | exact resolve eq188772 eq187713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187713 eq188772
  have eq188834 : False := by grind
  exact eq188834

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxx_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq174 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x x) X4 X5
       have i₂ := eq16 (M.op x x) x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x (M.op X1 X1)) X1 x x
       have i₂ := eq16 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | (have i₁ := eq16 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq178 x x X2 X3 X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq184 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq183 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq190 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op x x)
       have i₂ := eq179 (M.op x x) x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq179 x x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op x x) X2 X3
       have i₂ := eq179 (M.op x x) x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq180
  have eq224 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq206 eq184
    | exact resolve eq184 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq184 eq13
    | (have j0 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) x
       have r₂ := eq184 x
       grind)
    | exact resolve eq13 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq236 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq234 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq238 : ∀ X0 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq206 eq236
    | exact resolve eq236 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq236
  have eq243 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq190 eq238
    | exact resolve eq238 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq325 : (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) x) := by
    first
    | exact superpose eq243 eq141
    | exact resolve eq141 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq243 eq38
    | exact resolve eq38 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1117 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq194 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq194
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1153 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1166 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1187 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1166 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1166 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq1166 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq1166 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1166 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1228 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq490 eq1159
    | (have j0 := eq1159 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq1159 (σ (M.op (M.op x y) y))
       have r₂ := eq490 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq1159 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1237 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq1228
  have eq2284 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1145
       grind)
    | exact superpose eq1145 eq39
    | exact resolve eq39 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2285 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2284
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2284
    | exact resolve eq2284 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284
  have eq2287 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2285
    | exact resolve eq2285 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285
  have eq8214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1131 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1131
    | (have j0 := eq1131 (σ X0) (σ X1)
       grind)
    | exact resolve eq1131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8230 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8214 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq8214
    | (have j0 := eq8214 X0 X1
       grind)
    | exact resolve eq8214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8214
  have eq16003 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq1237 eq195
    | exact resolve eq195 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq16007 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (σ (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq1237 eq16003
    | exact resolve eq16003 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq16003
  have eq16019 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq190 eq16007
    | exact resolve eq16007 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq16007
  have eq16045 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq16019 eq15
    | exact resolve eq15 eq16019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2287 eq1153
    | exact resolve eq1153 eq2287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2287
  have eq18786 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq18778
       have r₂ := eq27
       grind)
    | exact resolve eq18778 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18778
  have eq18848 : (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18786 eq194
    | exact resolve eq194 eq18786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18852 : (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18786 eq18848
    | exact resolve eq18848 eq18786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18786 eq18848
  have eq18880 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18852 eq325
    | exact resolve eq325 eq18852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq18909 : (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18852 eq16045
    | exact resolve eq16045 eq18852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16045 eq18852
  have eq18953 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq18909
    | exact resolve eq18909 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18909
  have eq18977 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq18880
    | exact resolve eq18880 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18880
  have eq19003 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq18977
       have r₂ := eq12 x (σ x)
       grind)
    | (have r₁ := eq18977
       have r₂ := eq12 x x
       grind)
    | exact resolve eq18977 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18977
  have eq19023 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq19003 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq19003
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19003
       grind)
    | exact resolve eq13 eq19003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19003
  have eq19031 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq19023
  have eq19051 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq19031 eq141
    | exact resolve eq141 eq19031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19031
  have eq19062 : x = (k x x) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq19051
    | exact resolve eq19051 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19051
  have eq19067 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq1187 x y
       grind)
    | (have r₁ := eq19062
       have r₂ := eq1187 x x
       grind)
    | exact resolve eq19062 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq19062
  have eq19073 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1145
       have i₂ := eq19067
       grind)
    | exact superpose eq19067 eq1145
    | exact resolve eq1145 eq19067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq19075 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq19067
       grind)
    | exact superpose eq19067 eq39
    | exact resolve eq39 eq19067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19078 : y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq19073
  have eq19080 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq19075
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19075
    | exact resolve eq19075 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19075
  have eq19090 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq19080 eq1153
    | exact resolve eq1153 eq19080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19080
  have eq19107 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op y x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 y x X2 X0 X1
       have i₂ := eq19078
       grind)
    | exact superpose eq19078 eq174
    | exact resolve eq174 eq19078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19111 : (M.op (M.op x y) y) = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq194 y x
       have i₂ := eq19078
       grind)
    | exact superpose eq19078 eq194
    | exact resolve eq194 eq19078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19115 : y = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19078 eq19111
    | exact resolve eq19111 eq19078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19111
  have eq19119 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op y x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq19107 x x X2
       have i₂ := eq194 x x
       grind)
    | (have i₁ := eq19107 x y X2
       have i₂ := eq194 X2 x
       grind)
    | exact superpose eq194 eq19107
    | (have j0 := eq19107 x y X2
       grind)
    | exact resolve eq19107 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19107
  have eq19126 : ∀ X2 : G, y = (M.op X2 (M.op y x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq19115 eq19119
    | exact resolve eq19119 eq19115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19119
  have eq19128 : ∀ X2 : G, y = (M.op X2 y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq19078 eq19126
    | exact resolve eq19126 eq19078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19078 eq19126
  have eq19198 : y = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19115 eq16019
    | exact resolve eq16019 eq19115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19115
  have eq19250 : x = (M.op x x) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19198
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19198
    | exact resolve eq19198 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19198
  have eq19315 : (M.op (M.op x y) y) = (M.op x x) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq194 x x
       have i₂ := eq19250
       grind)
    | exact superpose eq19250 eq194
    | exact resolve eq194 eq19250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19321 : x = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19250 eq19315
    | exact resolve eq19315 eq19250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19250 eq19315
  have eq19360 : ∀ X0 : G, x = (M.op x X0) ∨ y = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19321 eq224
    | exact resolve eq224 eq19321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19392 : x = (σ x) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19321 eq16019
    | exact resolve eq16019 eq19321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19432 : x = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19321 eq194
    | exact resolve eq194 eq19321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19441 : y = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19432
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19432
    | exact resolve eq19432 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19432
  have eq19448 : x = (σ x) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19392
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19392
    | exact resolve eq19392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19392
  have eq19482 : (M.op x y) = (σ x) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19441 eq19448
    | exact resolve eq19448 eq19441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19448
  have eq19634 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19482 eq26
    | exact resolve eq26 eq19482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19635 : x = (τ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19482 eq29
    | exact resolve eq29 eq19482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19482
  have eq19739 : (M.op x y) = (τ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19441 eq19635
    | exact resolve eq19635 eq19441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19635
  have eq20113 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19739 eq14
    | exact resolve eq14 eq19739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19739
  have eq20169 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20113
    | exact resolve eq20113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20113
  have eq20567 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op x X0) ∨ y = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq194 x X0
       have i₂ := eq19360 X0
       grind)
    | exact superpose eq19360 eq194
    | exact resolve eq194 eq19360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19360
  have eq20587 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x y) X0) ∨ y = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19441 eq20567
    | exact resolve eq20567 eq19441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20567
  have eq20608 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19321 eq20587
    | exact resolve eq20587 eq19321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19321 eq20587
  have eq20621 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19441 eq20608
    | exact resolve eq20608 eq19441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19441 eq20608
  have eq21988 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20621 eq19634
    | exact resolve eq19634 eq20621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19634 eq20621
  have eq22020 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq21988
  have eq22142 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22020 eq27
    | exact resolve eq27 eq22020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22020
  have eq22155 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22142
       have r₂ := eq20169
       grind)
    | exact resolve eq22142 eq20169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20169 eq22142
  have eq22161 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22155
       grind)
    | exact superpose eq22155 eq18
    | exact resolve eq18 eq22155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22171 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (k (M.op (M.op x y) (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq243 X0
       have i₂ := eq22155
       grind)
    | exact superpose eq22155 eq243
    | exact resolve eq243 eq22155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq22219 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op x y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16019
       have i₂ := eq22155
       grind)
    | exact superpose eq22155 eq16019
    | exact resolve eq16019 eq22155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23982 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19128 x
       grind)
    | exact superpose eq19128 eq18
    | (have j1 := eq19128 x
       grind)
    | exact resolve eq18 eq19128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19128
  have eq24063 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq23982
  have eq24118 : (M.op (M.op x y) y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq194 x x
       have i₂ := eq24063
       grind)
    | exact superpose eq24063 eq194
    | exact resolve eq194 eq24063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24126 : (M.op x x) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22155 eq24118
    | exact resolve eq24118 eq22155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24118
  have eq24138 : x = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24063 eq24126
    | exact resolve eq24126 eq24063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24063 eq24126
  have eq24181 : x = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24138 eq22219
    | exact resolve eq22219 eq24138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24187 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq24138 eq174
    | exact resolve eq174 eq24138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24191 : (M.op (M.op x y) y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24138 eq194
    | exact resolve eq194 eq24138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24195 : x = (σ x) ∨ y = (M.op x y) := by grind
  clear eq24181
  have eq24203 : (M.op (M.op x y) (σ y)) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22155 eq24191
    | exact resolve eq24191 eq22155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24191
  have eq24207 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op x (σ y))) ∨ y = (M.op x y) := by
    intro X2
    first
    | (have i₁ := eq24187 x x X2
       have i₂ := eq194 x x
       grind)
    | (have i₁ := eq24187 x y X2
       have i₂ := eq194 X2 x
       grind)
    | exact superpose eq194 eq24187
    | (have j0 := eq24187 x y X2
       grind)
    | exact resolve eq24187 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24187
  have eq24209 : y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq24195
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24195
    | exact resolve eq24195 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24195
  have eq24211 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22161 eq24203
    | exact resolve eq24203 eq22161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24203
  have eq24214 : ∀ X2 : G, (M.op (M.op x y) (σ y)) = (M.op X2 (M.op x (σ y))) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq22155 eq24207
    | exact resolve eq24207 eq22155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22155 eq24207
  have eq24219 : ∀ X2 : G, (M.op (M.op x y) (σ y)) = (M.op X2 (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq22161 eq24214
    | exact resolve eq24214 eq22161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22161 eq24214
  have eq24221 : ∀ X2 : G, x = (M.op X2 (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq24138 eq24219
    | exact resolve eq24219 eq24138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24219
  have eq24223 : ∀ X2 : G, (σ x) = (M.op X2 (M.op x y)) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq24209 eq24221
    | exact resolve eq24221 eq24209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24221
  have eq25077 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24211 eq22171
    | exact resolve eq22171 eq24211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22171
  have eq25078 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24211 eq22219
    | exact resolve eq22219 eq24211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22219
  have eq25082 : (M.op x y) ≠ (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24211 eq13
    | (have j0 := eq13 (M.op x y) (σ y)
       grind)
    | (have r₁ := eq13 (M.op x y) (σ y)
       have r₂ := eq24211
       grind)
    | exact resolve eq13 eq24211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24211
  have eq25090 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq25082
  have eq25093 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq25078
  have eq25094 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq25077 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25077
  have eq25105 : (σ x) = (k (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24223 eq25090
    | exact resolve eq25090 eq24223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24223 eq25090
  have eq25107 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq25093
    | exact resolve eq25093 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25093
  have eq25110 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25094 eq25105
    | exact resolve eq25105 eq25094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25094 eq25105
  have eq25280 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25110 eq26
    | exact resolve eq26 eq25110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25396 : x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24138 eq25280
    | exact resolve eq25280 eq24138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24138 eq25280
  have eq25444 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24209 eq25396
    | exact resolve eq25396 eq24209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24209 eq25396
  have eq25488 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25110 eq25444
    | exact resolve eq25444 eq25110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25110 eq25444
  have eq25686 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25488 eq27
    | exact resolve eq27 eq25488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25488
  have eq25697 : y = (M.op x y) := by
    first
    | (have r₁ := eq25686
       have r₂ := eq25107
       grind)
    | exact resolve eq25686 eq25107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25107 eq25686
  have eq25702 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq18
    | exact resolve eq18 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25703 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq24
    | exact resolve eq24 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq25705 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq40
    | exact resolve eq40 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq25711 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq224 X0
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq224
    | exact resolve eq224 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq25760 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16019
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq16019
    | exact resolve eq16019 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq25792 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq19067
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq19067
    | exact resolve eq19067 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19067
  have eq25846 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25703 eq20
    | exact resolve eq20 eq25703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25849 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq25703 eq15
    | exact resolve eq15 eq25703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25703
  have eq26282 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq25702 eq16
    | exact resolve eq16 eq25702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26285 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq25702 eq175
    | exact resolve eq175 eq25702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28663 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq25711 X0
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq25711
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq25711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28739 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq28663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28663
  have eq30184 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq25792 eq39
    | exact resolve eq39 eq25792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq25792
  have eq30189 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq30184
    | exact resolve eq30184 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30184
  have eq30194 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq25846 eq30189
    | exact resolve eq30189 eq25846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30189
  have eq51181 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq28739 eq26282
    | exact resolve eq26282 eq28739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26282 eq28739
  have eq51220 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq51181
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq51181 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51181
  have eq51347 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq51220 eq25711
    | exact resolve eq25711 eq51220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25711
  have eq51351 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq51220 eq25760
    | exact resolve eq25760 eq51220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51400 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq51220 eq175
    | exact resolve eq175 eq51220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq51406 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq51220 eq26285
    | exact resolve eq26285 eq51220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26285
  have eq51411 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq51406 eq51400
    | exact resolve eq51400 eq51406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51400
  have eq51429 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq51351
    | exact resolve eq51351 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq51351
  have eq51444 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq25846 eq51429
    | exact resolve eq51429 eq25846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51429
  have eq51449 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq51444
    | exact resolve eq51444 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51444
  have eq51452 : (k (σ y) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq25846 eq51449
    | exact resolve eq51449 eq25846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51449
  have eq288528 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18953 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq18953
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq18953
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18953
       grind)
    | exact resolve eq13 eq18953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18953
  have eq288541 : (σ x) = (k (σ x) (σ x)) ∨ y = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq288528
  have eq288557 : (M.op x y) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq288541
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq288541
    | exact resolve eq288541 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288541
  have eq288578 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq288557
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq288557
    | exact resolve eq288557 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288557
  have eq288888 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq288578 eq141
    | exact resolve eq141 eq288578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288578
  have eq288947 : x = (k x x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq288888
    | exact resolve eq288888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288888
  have eq288957 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq1159 x
       grind)
    | (have r₁ := eq288947
       have r₂ := eq1159 x
       grind)
    | exact resolve eq288947 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159 eq288947
  have eq288975 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op x y) x)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | exact superpose eq288957 eq174
    | exact resolve eq174 eq288957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288984 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq288957 eq51411
    | exact resolve eq51411 eq288957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288986 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq288957 eq288984
    | exact resolve eq288984 eq288957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288984
  have eq288995 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op x y) x)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    intro X2
    first
    | (have i₁ := eq288975 x x X2
       have i₂ := eq194 x x
       grind)
    | (have i₁ := eq288975 x y X2
       have i₂ := eq194 X2 x
       grind)
    | exact superpose eq194 eq288975
    | (have j0 := eq288975 x y X2
       grind)
    | exact resolve eq288975 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288975
  have eq289006 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) x)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    intro X2
    first
    | (have i₁ := eq288995 X2
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq288995
    | exact resolve eq288995 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288995
  have eq289014 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) x)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    intro X2
    first
    | exact superpose eq51220 eq289006
    | exact resolve eq289006 eq51220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289006
  have eq289020 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    intro X2
    first
    | exact superpose eq288957 eq289014
    | exact resolve eq289014 eq288957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288957 eq289014
  have eq289022 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    intro X2
    first
    | exact superpose eq288986 eq289020
    | exact resolve eq289020 eq288986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288986 eq289020
  have eq289367 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq289022 eq25760
    | exact resolve eq25760 eq289022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25760 eq289022
  have eq289459 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq289367
    | exact resolve eq289367 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289367
  have eq289504 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25846 eq289459
    | exact resolve eq289459 eq25846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289459
  have eq289505 : x = (M.op x x) ∨ (M.op x y) = (σ y) := by grind
  clear eq289504
  have eq289546 : x ≠ x ∨ x = (k x x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq289505
       grind)
    | exact superpose eq289505 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq289505
       grind)
    | exact resolve eq13 eq289505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289557 : (k (M.op x y) (M.op x y)) = (M.op x x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq51411 x x
       have i₂ := eq289505
       grind)
    | exact superpose eq289505 eq51411
    | exact resolve eq51411 eq289505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289559 : x = (k x x) ∨ (M.op x y) = (σ y) := by grind
  clear eq289546
  have eq289562 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq289505 eq289557
    | exact resolve eq289557 eq289505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289505 eq289557
  have eq289642 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq8230 x x
       have i₂ := eq289559
       grind)
    | exact superpose eq289559 eq8230
    | (have j0 := eq8230 x x
       grind)
    | exact resolve eq8230 eq289559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8230 eq289559
  have eq289663 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ y) := by grind
  clear eq289642
  have eq289664 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ y) := by grind
  clear eq289663
  have eq289674 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq289664
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq289664
    | exact resolve eq289664 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289664
  have eq289759 : (k (M.op x y) (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq289674 eq51411
    | exact resolve eq51411 eq289674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289764 : x = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq289562 eq289759
    | exact resolve eq289759 eq289562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289759
  have eq289782 : (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq289674 eq289764
    | exact resolve eq289764 eq289674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289674 eq289764
  have eq290739 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq289562 eq51347
    | exact resolve eq51347 eq289562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51347
  have eq291050 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq289562 eq25705
    | exact resolve eq25705 eq289562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291183 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq291050
    | exact resolve eq291050 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291050
  have eq291444 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq289782 eq290739
    | exact resolve eq290739 eq289782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289782 eq290739
  have eq291515 : (σ x) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq25846 eq291183
    | exact resolve eq291183 eq25846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291183
  have eq291580 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq51452 eq291515
    | exact resolve eq291515 eq51452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291515
  have eq291610 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq291580
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq291580
    | exact resolve eq291580 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291580
  have eq294756 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq291444 eq26
    | (have j1 := eq291444 (σ y)
       grind)
    | exact resolve eq26 eq291444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291444
  have eq294965 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq294756 eq27
    | exact resolve eq27 eq294756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294756
  have eq294992 : (σ x) ≠ (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq25846 eq294965
    | exact resolve eq294965 eq25846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294965
  have eq295656 : (M.op (M.op x y) y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq289562 eq1135
    | (have j0 := eq1135 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1135 eq289562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq289562
  have eq295929 : (M.op (M.op x y) y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq295656
  have eq295993 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq25702 eq295929
    | exact resolve eq295929 eq25702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295929
  have eq296130 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq295993
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq295993
    | exact resolve eq295993 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295993
  have eq296131 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq296130
  have eq296245 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq51220 eq296131
    | exact resolve eq296131 eq51220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296131
  have eq297556 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq296245 eq25705
    | exact resolve eq25705 eq296245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25705 eq296245
  have eq297670 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq297556
    | exact resolve eq297556 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297556
  have eq297703 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq25846 eq297670
    | exact resolve eq297670 eq25846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25846 eq297670
  have eq297731 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq51452 eq297703
    | exact resolve eq297703 eq51452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51452 eq297703
  have eq297759 : (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq291610 eq297731
    | exact resolve eq297731 eq291610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291610 eq297731
  have eq297782 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq297759
       have r₂ := eq294992
       grind)
    | exact resolve eq297759 eq294992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294992 eq297759
  have eq297802 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq297782 eq26
    | exact resolve eq26 eq297782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq297856 : (M.op (σ x) (σ y)) = (k (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq297782 eq1153
    | exact resolve eq1153 eq297782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq298020 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq297782 eq25849
    | exact resolve eq25849 eq297782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25849
  have eq298039 : (M.op x y) = (k (M.op x y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq297782 eq30194
    | exact resolve eq30194 eq297782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30194
  have eq298352 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq298020 eq14
    | exact resolve eq14 eq298020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298020
  have eq298545 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq298352 eq20
    | exact resolve eq20 eq298352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq349653 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq297856 eq298039
    | exact resolve eq298039 eq297856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297856 eq298039
  have eq403350 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq19090 eq174
    | exact resolve eq174 eq19090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403359 : (k (M.op x y) (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq19090 eq51411
    | exact resolve eq51411 eq19090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19090
  have eq403364 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq297782 eq403359
    | exact resolve eq403359 eq297782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403359
  have eq403373 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq297782 eq403350
    | exact resolve eq403350 eq297782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403350
  have eq403382 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq297782 eq403364
    | exact resolve eq403364 eq297782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403364
  have eq403391 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X2
    first
    | (have i₁ := eq403373 x x X2
       have i₂ := eq194 x x
       grind)
    | (have i₁ := eq403373 x y X2
       have i₂ := eq194 X2 x
       grind)
    | exact superpose eq194 eq403373
    | (have j0 := eq403373 x y X2
       grind)
    | exact resolve eq403373 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403373
  have eq403396 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq403382
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq403382
    | exact resolve eq403382 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403382
  have eq403405 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X2
    first
    | (have i₁ := eq403391 X2
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq403391
    | exact resolve eq403391 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403391
  have eq403410 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq349653 eq403396
    | exact resolve eq403396 eq349653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403396
  have eq403419 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X2
    first
    | exact superpose eq51220 eq403405
    | exact resolve eq403405 eq51220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403405
  have eq403431 : ∀ X2 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (k (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X2
    first
    | exact superpose eq297782 eq403419
    | (have j0 := eq403419 X2
       grind)
    | exact resolve eq403419 eq297782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297782 eq403419
  have eq403442 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (k (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X2
    first
    | (have i₁ := eq403431 X2
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq403431
    | (have j0 := eq403431 X2
       grind)
    | exact resolve eq403431 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403431
  have eq403449 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (k (M.op x y) (M.op x y)) = (M.op X2 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X2
    first
    | exact superpose eq349653 eq403442
    | exact resolve eq403442 eq349653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349653 eq403442
  have eq403451 : ∀ X2 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X2
    first
    | exact superpose eq403410 eq403449
    | exact resolve eq403449 eq403410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403410 eq403449
  have eq411128 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq403451 eq13
    | (have j1 := eq403451 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq403451 x
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq403451 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq403451 x
       grind)
    | exact resolve eq13 eq403451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403451
  have eq411143 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq411128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411128
  have eq411261 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq411143 eq141
    | (have j1 := eq411143 X0
       grind)
    | exact resolve eq141 eq411143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq411143
  have eq411327 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq29 eq411261
    | (have j0 := eq411261 X0
       grind)
    | exact resolve eq411261 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq411261
  have eq411440 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X3 (M.op x y)) ∨ x = (k x x) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq411327 eq174
    | (have j1 := eq411327 X3
       grind)
    | exact resolve eq174 eq411327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq411449 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq411327 eq51411
    | (have j1 := eq411327 X0
       grind)
    | exact resolve eq51411 eq411327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411452 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq411327 eq411449
    | (have j0 := eq411449 X0
       have j1 := eq411327 X0
       grind)
    | exact resolve eq411449 eq411327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411449
  have eq411461 : ∀ X2 X3 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X3 (M.op x y)) ∨ x = (k x x) := by
    intro X2 X3
    first
    | (have i₁ := eq411440 x x X2 X3
       have i₂ := eq194 x x
       grind)
    | (have i₁ := eq411440 x y X2 X3
       have i₂ := eq194 X2 X3
       grind)
    | exact superpose eq194 eq411440
    | (have j0 := eq411440 x y X2 X3
       grind)
    | exact resolve eq411440 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq411440
  have eq411472 : ∀ X2 X3 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X3 (M.op x y)) ∨ x = (k x x) := by
    intro X2 X3
    first
    | (have i₁ := eq411461 X2 X3
       have i₂ := eq25697
       grind)
    | exact superpose eq25697 eq411461
    | (have j0 := eq411461 X2 X3
       grind)
    | exact resolve eq411461 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25697 eq411461
  have eq411480 : ∀ X2 X3 : G, (k (M.op x y) (M.op x y)) = (M.op X2 (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X3 (M.op x y)) ∨ x = (k x x) := by
    intro X2 X3
    first
    | exact superpose eq51220 eq411472
    | (have j0 := eq411472 X2 X3
       grind)
    | exact resolve eq411472 eq51220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51220 eq411472
  have eq411486 : ∀ X2 X3 : G, (k (M.op x y) (M.op x y)) = (M.op X2 (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X3 (M.op x y)) ∨ x = (k x x) := by
    intro X2 X3
    first
    | exact superpose eq411327 eq411480
    | (have j0 := eq411480 X2 X3
       have j1 := eq411327 X3
       grind)
    | exact resolve eq411480 eq411327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411327 eq411480
  have eq411489 : ∀ X2 X3 : G, (M.op x y) = (M.op X3 (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X2 (M.op x y)) ∨ x = (k x x) := by
    intro X2 X3
    first
    | exact superpose eq411452 eq411486
    | (have j0 := eq411486 X2 X3
       have j1 := eq411452 X3
       grind)
    | exact resolve eq411486 eq411452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411452 eq411486
  have eq412756 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq411489 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411489
  have eq412757 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq412756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412756
  have eq413020 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq412757 eq297802
    | exact resolve eq297802 eq412757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412757
  have eq413029 : x = (k x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq413020
  have eq413075 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1131 x x
       have i₂ := eq413029
       grind)
    | exact superpose eq413029 eq1131
    | (have j0 := eq1131 x x
       grind)
    | (have r₁ := eq1131 x x
       have r₂ := eq413029
       grind)
    | exact resolve eq1131 eq413029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq413029
  have eq413103 : x ≠ x ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq413075
  have eq413104 : x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq413103
  have eq413195 : (k (M.op x y) (M.op x y)) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51411 x x
       have i₂ := eq413104
       grind)
    | exact superpose eq413104 eq51411
    | exact resolve eq51411 eq413104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51411
  have eq413201 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq413104 eq413195
    | exact resolve eq413195 eq413104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413104 eq413195
  have eq422564 : x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq413201 eq51406
    | exact resolve eq51406 eq413201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51406 eq413201
  have eq422998 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25702 eq422564
    | exact resolve eq422564 eq25702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422564
  have eq423261 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq422998 eq27
    | exact resolve eq27 eq422998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422998
  have eq423302 : x = (M.op x y) := by
    first
    | (have r₁ := eq423261
       have r₂ := eq298545
       grind)
    | exact resolve eq423261 eq298545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423261
  have eq423305 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq423302
       grind)
    | exact superpose eq423302 eq22
    | exact resolve eq22 eq423302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq423419 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq25702
       have i₂ := eq423302
       grind)
    | exact superpose eq423302 eq25702
    | exact resolve eq25702 eq423302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25702 eq423302
  have eq423621 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq298352 eq423305
    | exact resolve eq423305 eq298352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298352 eq423305
  have eq424002 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq423621 eq297802
    | exact resolve eq297802 eq423621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297802 eq423621
  have eq424064 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq423419 eq424002
    | exact resolve eq424002 eq423419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423419 eq424002
  have eq424462 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq424064 eq27
    | exact resolve eq27 eq424064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq424064
  have eq424502 : False := by grind
  exact eq424502

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_pxx_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq180 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | (have i₁ := eq16 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq180 x x X2 X3 X5
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq180
    | exact resolve eq180 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq188 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq187 x x X5
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq187
    | exact resolve eq187 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq193 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq181
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq205 eq188
    | exact resolve eq188 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq188 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 x (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq188 x
       grind)
    | exact resolve eq13 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq239 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq205 eq235
    | exact resolve eq235 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq461 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq239 eq34
    | exact resolve eq34 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq489 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq461 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq461
    | exact resolve eq461 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq535 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq536 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq639 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq639 X0
       have i₂ := eq182 X0 X0
       grind)
    | exact superpose eq182 eq639
    | (have j0 := eq639 X0
       grind)
    | exact resolve eq639 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq644 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq205 eq641
    | (have j0 := eq641 X0
       grind)
    | exact resolve eq641 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq645 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq644 X0
       have i₂ := eq182 (M.op X0 X0) X0
       grind)
    | exact superpose eq182 eq644
    | (have j0 := eq644 X0
       grind)
    | exact resolve eq644 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq644
  have eq646 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op X0 X0) X0) ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | exact superpose eq205 eq645
    | (have j0 := eq645 (k (M.op X0 X0) X0)
       grind)
    | exact resolve eq645 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq721 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq749 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq489 eq574
    | (have j0 := eq574 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq574 (σ (M.op (M.op x y) y))
       have r₂ := eq489 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq574 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq749
  have eq814 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq239 eq721
    | exact resolve eq721 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq844 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq814 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq814
    | exact resolve eq814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq853 : (τ (M.op (M.op x y) y)) ≠ (τ (M.op (M.op x y) y)) ∨ (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq844 eq574
    | (have j0 := eq574 (τ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq574 (τ (M.op (M.op x y) y))
       have r₂ := eq844 (τ (M.op (M.op x y) y))
       grind)
    | exact resolve eq574 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by grind
  clear eq853
  have eq1899 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq535
       grind)
    | exact superpose eq535 eq39
    | exact resolve eq39 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq1900 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1899
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1899
    | exact resolve eq1899 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899
  have eq1902 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1900
    | exact resolve eq1900 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq2048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1902 eq536
    | exact resolve eq536 eq1902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2055 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2048
       have r₂ := eq27
       grind)
    | exact resolve eq2048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2072 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2055 eq181
    | exact resolve eq181 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2190 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2072 eq26
    | (have j1 := eq2072 (σ x)
       grind)
    | exact resolve eq26 eq2072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2229 : ∀ X0 : G, y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2190 eq239
    | exact resolve eq239 eq2190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq2448 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X1 (M.op (σ x) (σ y))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq2229 X1
       grind)
    | exact superpose eq2229 eq181
    | (have j1 := eq2229 X1
       grind)
    | exact resolve eq181 eq2229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3065 : (k (σ y) (σ x)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2055 eq646
    | (have j0 := eq646 (k (σ y) (σ x))
       grind)
    | exact resolve eq646 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq3082 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) ∨ (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq489 (M.op (σ (M.op sF0 y)) (σ (M.op sF0 y)))
       have i₂ := eq646 (σ (M.op sF0 y))
       grind)
    | exact superpose eq646 eq489
    | (have j1 := eq646 (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y)))
       grind)
    | exact resolve eq489 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq3089 : (M.op (M.op x y) y) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) ∨ (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq844 (M.op (τ (M.op sF0 y)) (τ (M.op sF0 y)))
       have i₂ := eq646 (τ (M.op sF0 y))
       grind)
    | exact superpose eq646 eq844
    | (have j1 := eq646 (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y)))
       grind)
    | exact resolve eq844 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq3095 : (σ (M.op (M.op x y) y)) = (k (σ (M.op x x)) (σ x)) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq646 x
       grind)
    | exact superpose eq646 eq39
    | (have j1 := eq646 x
       grind)
    | exact resolve eq39 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq646
  have eq3111 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) ∨ (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq862 eq3089
    | exact resolve eq3089 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq3089
  have eq3112 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by grind
  clear eq3111
  have eq3122 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) ∨ (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq753 eq3082
    | exact resolve eq3082 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq3082
  have eq3123 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by grind
  clear eq3122
  have eq3146 : (σ x) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1902 eq3065
    | exact resolve eq3065 eq1902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902 eq3065
  have eq3678 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq2448 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq2448 X0 (M.op x y)
       grind)
    | exact superpose eq2448 eq18
    | (have j1 := eq2448 x X0
       grind)
    | exact resolve eq18 eq2448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq38496 : ∀ X0 : G, (k (σ y) (σ x)) = (σ (M.op (M.op x y) y)) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3095
       have i₂ := eq2229 X0
       grind)
    | exact superpose eq2229 eq3095
    | (have j1 := eq2229 X0
       grind)
    | exact resolve eq3095 eq2229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229 eq3095
  have eq38514 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3123 eq38496
    | (have j0 := eq38496 X0
       grind)
    | exact resolve eq38496 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38496
  have eq38523 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38514 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38514
    | (have j0 := eq38514 X0
       grind)
    | exact resolve eq38514 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38514
  have eq38529 : ∀ X0 : G, (M.op x y) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3678 eq38523
    | (have j0 := eq38523 X0
       have j1 := eq3678 X0
       grind)
    | exact resolve eq38523 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38523
  have eq38532 : ∀ X0 : G, (M.op x y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3678 eq38529
    | (have j0 := eq38529 X0
       have j1 := eq3678 X0
       grind)
    | exact resolve eq38529 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38529
  have eq38533 : ∀ X0 : G, (M.op x y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq38532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38532
  have eq38601 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq536
       have i₂ := eq38533 (k sF3 sF2)
       grind)
    | exact superpose eq38533 eq536
    | (have j1 := eq38533 X0
       grind)
    | exact resolve eq536 eq38533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq38533
  have eq38607 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq38601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38601
  have eq40282 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq38607 (M.op X1 X1)
       grind)
    | exact superpose eq38607 eq181
    | (have j1 := eq38607 X1
       grind)
    | exact resolve eq181 eq38607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38607
  have eq40370 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3678 eq40282
    | (have j0 := eq40282 X0 X1
       have j1 := eq3678 X1
       grind)
    | exact resolve eq40282 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3678 eq40282
  have eq40522 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq40370 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq40370 eq26
    | (have j1 := eq40370 (σ x) X0
       grind)
    | exact resolve eq26 eq40370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40370
  have eq40537 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq40522 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40522
  have eq40613 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40537 eq574
    | (have j0 := eq574 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq574 (M.op (σ x) (σ y))
       have r₂ := eq40537 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq574 eq40537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq40537
  have eq40640 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq40613
  have eq40746 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40640 eq193
    | exact resolve eq193 eq40640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq40802 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40640 eq40746
    | exact resolve eq40746 eq40640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40640 eq40746
  have eq48641 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2190 eq3146
    | exact resolve eq3146 eq2190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190 eq3146
  have eq48888 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq48641
  have eq48923 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq48888
       have r₂ := eq27
       grind)
    | exact resolve eq48888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48888
  have eq48948 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq48923
       grind)
    | exact superpose eq48923 eq181
    | exact resolve eq181 eq48923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq48923
  have eq49381 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq48948 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq48948 x
       grind)
    | exact superpose eq48948 eq18
    | (have j1 := eq48948 x
       grind)
    | exact resolve eq18 eq48948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48948
  have eq49878 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49381 eq3123
    | exact resolve eq3123 eq49381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49900 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49381 eq40802
    | exact resolve eq40802 eq49381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40802 eq49381
  have eq49973 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq49900
  have eq50032 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq49878
    | exact resolve eq49878 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49878
  have eq50225 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq50032 eq188
    | exact resolve eq188 eq50032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50226 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50032 eq205
    | exact resolve eq205 eq50032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50233 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq50226
    | exact resolve eq50226 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50226
  have eq50234 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq50225
    | (have j0 := eq50225 X0
       grind)
    | exact resolve eq50225 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50225
  have eq50237 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50032 eq50233
    | exact resolve eq50233 eq50032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50233
  have eq50238 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq50032 eq50234
    | exact resolve eq50234 eq50032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50032 eq50234
  have eq50241 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49973 eq188
    | exact resolve eq188 eq49973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq50242 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49973 eq205
    | exact resolve eq205 eq49973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq50246 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq50250 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq50242
    | exact resolve eq50242 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50242
  have eq50251 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq50241
    | (have j0 := eq50241 X0
       grind)
    | exact resolve eq50241 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50241
  have eq50254 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49973 eq50250
    | exact resolve eq50250 eq49973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50250
  have eq50255 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49973 eq50251
    | exact resolve eq50251 eq49973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49973 eq50251
  have eq54211 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50237 eq3112
    | exact resolve eq3112 eq50237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50237
  have eq54396 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq54211
    | exact resolve eq54211 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54211
  have eq55825 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50254 eq3112
    | exact resolve eq3112 eq50254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112 eq50254
  have eq56011 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq55825
    | exact resolve eq55825 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq55825
  have eq56220 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56011 eq27
    | exact resolve eq27 eq56011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56011
  have eq56633 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq56220
       have r₂ := eq54396
       grind)
    | exact resolve eq56220 eq54396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54396 eq56220
  have eq56674 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq56633
       grind)
    | exact superpose eq56633 eq18
    | exact resolve eq18 eq56633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56717 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq56633
  have eq56847 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56674 eq50238
    | exact resolve eq50238 eq56674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50238
  have eq56923 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq56847
  have eq56939 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq56923
       have r₂ := eq56717
       grind)
    | exact resolve eq56923 eq56717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56717 eq56923
  have eq57224 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50255 eq56674
    | exact resolve eq56674 eq50255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50255 eq56674
  have eq57517 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq57224
  have eq57586 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq57517
       have r₂ := eq50246
       grind)
    | exact resolve eq57517 eq50246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50246 eq57517
  have eq58204 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57586 eq27
    | exact resolve eq27 eq57586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57586
  have eq58639 : x = (M.op x y) := by
    first
    | (have r₁ := eq58204
       have r₂ := eq56939
       grind)
    | exact resolve eq58204 eq56939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56939 eq58204
  have eq58710 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq58639
       grind)
    | exact superpose eq58639 eq18
    | exact resolve eq18 eq58639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq58711 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq58639
       grind)
    | exact superpose eq58639 eq22
    | exact resolve eq22 eq58639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq58639
  have eq58929 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq58710 eq223
    | exact resolve eq223 eq58710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq58978 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq58710 eq3123
    | exact resolve eq3123 eq58710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123 eq58710
  have eq59244 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq58978 eq58711
    | exact resolve eq58711 eq58978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58711
  have eq59245 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq58978 eq20
    | exact resolve eq20 eq58978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq58978
  have eq59373 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq59244 eq26
    | exact resolve eq26 eq59244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq59244
  have eq59476 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq58929 eq59373
    | exact resolve eq59373 eq58929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58929 eq59373
  have eq59567 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq59476 eq27
    | exact resolve eq27 eq59476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq59476
  have eq59755 : False := by grind
  exact eq59755

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pyy_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq24
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
  clear eq43
  have eq60 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | (have i₁ := eq14 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq213 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (M.op x x)
       have i₂ := eq61 (M.op x x) x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq61 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq62 x x
       have i₂ := eq61 x x
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq457 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq60 x x X2 X3 X5
       have i₂ := eq61 x x
       grind)
    | exact superpose eq61 eq60
    | exact resolve eq60 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq458 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X5) := by
    intro X5
    first
    | (have i₁ := eq457 x x X5
       have i₂ := eq61 x x
       grind)
    | exact superpose eq61 eq457
    | exact resolve eq457 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq470 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq458 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 x (M.op (M.op x y) y)
       have r₂ := eq458 x
       grind)
    | exact resolve eq13 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq470 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq633 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq635 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq3567 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq476 eq635
    | (have j0 := eq635 (M.op (M.op x y) y)
       grind)
    | exact resolve eq635 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3579 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq635 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq635
    | (have j0 := eq635 (τ X0)
       grind)
    | exact resolve eq635 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq635
  have eq3591 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq3567
  have eq3596 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3579 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3579
    | (have j0 := eq3579 X0
       grind)
    | exact resolve eq3579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3606 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3596 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3596
    | (have j0 := eq3596 X0
       grind)
    | exact resolve eq3596 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3596
  have eq10436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq10437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10436
    | exact resolve eq10436 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10436
  have eq10448 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10437
       have r₂ := eq27
       grind)
    | exact resolve eq10437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10437
  have eq10450 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10448
    | exact resolve eq10448 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10448
  have eq10575 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10450 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq10450
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10450
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10450
       grind)
    | exact resolve eq13 eq10450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10450
  have eq10576 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq10575
  have eq10586 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10576 eq49
    | exact resolve eq49 eq10576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10576
  have eq10621 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq10586
    | exact resolve eq10586 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10586
  have eq10624 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3606 x
       grind)
    | (have r₁ := eq10621
       have r₂ := eq3606 x
       grind)
    | exact resolve eq10621 eq3606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3606 eq10621
  have eq10759 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x
       have i₂ := eq10624
       grind)
    | exact superpose eq10624 eq61
    | exact resolve eq61 eq10624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11041 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq10759 eq10759
    | exact resolve eq10759 eq10759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10759
  have eq11082 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq11041 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11041
  have eq13495 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10624
       have i₂ := eq11082 x X0
       grind)
    | (have i₁ := eq10624
       have i₂ := eq11082 X0 x
       grind)
    | exact superpose eq11082 eq10624
    | exact resolve eq10624 eq11082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10624 eq11082
  have eq13497 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13495 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13495
  have eq13545 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13497 (M.op x x)
       have i₂ := eq215 x x
       grind)
    | exact superpose eq215 eq13497
    | exact resolve eq13497 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13497
  have eq13613 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13545 eq215
    | exact resolve eq215 eq13545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13545
  have eq13624 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13613
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13613
    | exact resolve eq13613 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13613
  have eq13625 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13624
  have eq13634 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13625 eq224
    | exact resolve eq224 eq13625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq13638 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13634
    | exact resolve eq13634 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13634
  have eq13642 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13638 eq213
    | exact resolve eq213 eq13638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq13646 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13638 eq458
    | exact resolve eq458 eq13638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13647 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13638 eq476
    | exact resolve eq476 eq13638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq13638
  have eq13679 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13625 eq13642
    | exact resolve eq13642 eq13625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13642
  have eq13702 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13679
  have eq13867 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13625 eq13646
    | exact resolve eq13646 eq13625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13646
  have eq13910 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13867 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13867
  have eq13918 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13625 eq13647
    | exact resolve eq13647 eq13625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13625 eq13647
  have eq13942 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13918 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13918
  have eq14226 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13702 (M.op x sF2)
       have i₂ := eq215 x sF2
       grind)
    | exact superpose eq215 eq13702
    | exact resolve eq13702 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13702
  have eq14347 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13942 eq49
    | exact resolve eq49 eq13942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq13942
  have eq14423 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq14347
    | exact resolve eq14347 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq14347
  have eq15361 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq14423
       grind)
    | exact superpose eq14423 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq14423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14423
  have eq15362 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq15361
  have eq15880 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x
       have i₂ := eq15362
       grind)
    | exact superpose eq15362 eq61
    | exact resolve eq61 eq15362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq24957 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15880 eq14226
    | exact resolve eq14226 eq15880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14226 eq15880
  have eq24992 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24957 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24957
  have eq25445 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15362
       have i₂ := eq24992 x
       grind)
    | exact superpose eq24992 eq15362
    | exact resolve eq15362 eq24992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15362 eq24992
  have eq25460 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq25445
  have eq25580 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq25460 eq13910
    | exact resolve eq13910 eq25460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13910 eq25460
  have eq25629 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq25580 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25580
  have eq26727 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25629 y
       grind)
    | exact superpose eq25629 eq18
    | (have j1 := eq25629 y
       grind)
    | exact resolve eq18 eq25629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25629
  have eq26789 : x = (M.op x y) := by grind
  clear eq26727
  have eq26812 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq26789 eq20
    | exact resolve eq20 eq26789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26869 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq26789 eq458
    | exact resolve eq458 eq26789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq26895 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26789 eq3591
    | exact resolve eq3591 eq26789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3591
  have eq26897 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq26895
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26895
    | exact resolve eq26895 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26895
  have eq26923 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq26869 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26869
    | (have j0 := eq26869 X0
       grind)
    | exact resolve eq26869 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26869
  have eq26978 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq26812
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26812
    | exact resolve eq26812 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26812
  have eq26979 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq26897
    | exact resolve eq26897 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq26897
  have eq26996 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq26789 eq26923
    | exact resolve eq26923 eq26789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26923
  have eq27021 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26978 eq26
    | exact resolve eq26 eq26978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq26978
  have eq27204 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26979 eq215
    | exact resolve eq215 eq26979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq27214 : (σ (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq26979 eq27204
    | exact resolve eq27204 eq26979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26979 eq27204
  have eq27222 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26789 eq27214
    | exact resolve eq27214 eq26789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27214
  have eq27230 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq27222
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27222
    | exact resolve eq27222 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq27222
  have eq27238 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq26789 eq27230
    | exact resolve eq27230 eq26789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26789 eq27230
  have eq28137 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq27238 eq27021
    | exact resolve eq27021 eq27238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27021
  have eq28138 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28137
       have i₂ := eq26996 sF3
       grind)
    | exact superpose eq26996 eq28137
    | exact resolve eq28137 eq26996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26996 eq28137
  have eq28140 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq28138 eq27
    | exact resolve eq27 eq28138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28138
  have eq28176 : False := by grind
  exact eq28176

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxy_pyx_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
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
  clear eq18
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) = (k (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    grind
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq67 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq295 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq423 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq295 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq295
    | (have j0 := eq295 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq295 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq425 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq295 (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq295
    | (have j0 := eq295 (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq295 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq426 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq295 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq295
    | (have j0 := eq295 (σ X0) (σ X1)
       grind)
    | exact resolve eq295 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq450 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq6531 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))
       have i₂ := eq450 X0 X1
       grind)
    | exact superpose eq450 eq9
    | exact resolve eq9 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6542 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6531 X0 X1 X2
       have i₂ := eq450 X0 X1
       grind)
    | exact superpose eq450 eq6531
    | exact resolve eq6531 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6531
  have eq6551 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6542 X0 X1 X2
       have i₂ := eq450 X0 X1
       grind)
    | exact superpose eq450 eq6542
    | exact resolve eq6542 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq6542
  have eq9876 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq426 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq9877 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq9876 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9876
  have eq10291 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq9877 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq9877
    | (have j0 := eq9877 (τ X0)
       grind)
    | exact resolve eq9877 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9877
  have eq10321 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq10291 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10291
    | (have j0 := eq10291 X0
       grind)
    | exact resolve eq10291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10291
  have eq10336 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10321 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10321
    | (have j0 := eq10321 X0
       grind)
    | exact resolve eq10321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10321
  have eq10363 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10336 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq10336
    | (have j0 := eq10336 (τ X0)
       grind)
    | exact resolve eq10336 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq10336
  have eq10393 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10363 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10363
    | (have j0 := eq10363 X0
       grind)
    | exact resolve eq10363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10363
  have eq10408 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10393 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10393
    | (have j0 := eq10393 X0
       grind)
    | exact resolve eq10393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10393
  have eq11408 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq423 x y
       grind)
    | exact superpose eq423 eq16
    | (have j1 := eq423 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq423 x y
       grind)
    | exact resolve eq16 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11448 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq423
  have eq11487 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11448 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11448
  have eq11496 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11408
  have eq11499 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11487 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq11487
    | (have j0 := eq11487 X0
       grind)
    | exact resolve eq11487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11487
  have eq11519 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq11499
  have eq23190 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11496
  have eq23256 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23190
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq23190
    | exact resolve eq23190 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23190
  have eq23265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq23256
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq23256 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23256
  have eq23270 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23265
       have r₂ := eq16
       grind)
    | exact resolve eq23265 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23265
  have eq23274 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23270
       grind)
    | exact superpose eq23270 eq16
    | exact resolve eq16 eq23270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23275 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq23270
       grind)
    | exact superpose eq23270 eq9
    | exact resolve eq9 eq23270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23270
  have eq32669 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq23275 (σ y)
       grind)
    | exact superpose eq23275 eq9
    | exact resolve eq9 eq23275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23275
  have eq33161 : (τ (M.op (σ y) (σ y))) = (k (τ (σ y)) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 y
       have i₂ := eq32669 (σ y)
       grind)
    | exact superpose eq32669 eq66
    | exact resolve eq66 eq32669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33249 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33161
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq33161
    | exact resolve eq33161 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33161
  have eq33293 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32669 eq33249
    | exact resolve eq33249 eq32669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32669 eq33249
  have eq33300 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33293
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq33293
    | exact resolve eq33293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33293
  have eq33312 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq33300
       grind)
    | exact superpose eq33300 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq33300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33300
  have eq33313 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq33312
  have eq33326 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq33313
       grind)
    | exact superpose eq33313 eq9
    | exact resolve eq9 eq33313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33462 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq33313 eq33326
    | exact resolve eq33326 eq33313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33326
  have eq33531 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq33313 eq33462
    | exact resolve eq33462 eq33313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33313 eq33462
  have eq33539 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq33531 eq23274
    | (have j1 := eq33531 x
       grind)
    | exact resolve eq23274 eq33531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23274 eq33531
  have eq33613 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq33539
  have eq33618 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  have eq37289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11519 x
       have i₂ := eq33613
       grind)
    | exact superpose eq33613 eq11519
    | (have j0 := eq11519 x
       grind)
    | exact resolve eq11519 eq33613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11519
  have eq37421 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq37289
       have r₂ := eq16
       grind)
    | exact resolve eq37289 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37289
  have eq37451 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq37421
       grind)
    | exact superpose eq37421 eq66
    | exact resolve eq66 eq37421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq37595 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37451
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37451
    | exact resolve eq37451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37451
  have eq37665 : (k x x) = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37421 eq37595
    | exact resolve eq37595 eq37421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37421 eq37595
  have eq37671 : x = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37665
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq37665
    | exact resolve eq37665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37665
  have eq37686 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq37671
       grind)
    | exact superpose eq37671 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq37671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37671
  have eq37687 : x = (M.op x y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq37686
  have eq37698 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq37687
       grind)
    | exact superpose eq37687 eq9
    | exact resolve eq9 eq37687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37687
  have eq40384 : ∀ X0 : G, x = (M.op x x) ∨ x = y ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq37698 y
       grind)
    | exact superpose eq37698 eq9
    | exact resolve eq9 eq37698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37698
  have eq40767 : ∀ X0 : G, x = y ∨ x = (M.op x y) ∨ x = y ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq33613
       have i₂ := eq40384 X0
       grind)
    | exact superpose eq40384 eq33613
    | (have j1 := eq40384 x
       grind)
    | exact resolve eq33613 eq40384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40384
  have eq40839 : ∀ X0 : G, x = (M.op x y) ∨ x = y ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq40767 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40767
  have eq41084 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have j0 := eq40839 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40839
  have eq41085 : x = (M.op x y) ∨ x = y := by grind
  clear eq41084
  have eq41089 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq41085 eq33613
    | exact resolve eq33613 eq41085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33613
  have eq41090 : (M.op x x) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41085 eq33618
    | exact resolve eq33618 eq41085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33618
  have eq41100 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq41085
       grind)
    | exact superpose eq41085 eq9
    | exact resolve eq9 eq41085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41085
  have eq41240 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41089 eq41090
    | exact resolve eq41090 eq41089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41089 eq41090
  have eq41269 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq41100 y
       grind)
    | exact superpose eq41100 eq9
    | exact resolve eq9 eq41100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41284 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq6551 y x X0
       have i₂ := eq41100 y
       grind)
    | exact superpose eq41100 eq6551
    | exact resolve eq6551 eq41100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6551 eq41100
  have eq42032 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq41284 (σ x)
       grind)
    | exact superpose eq41284 eq16
    | exact resolve eq16 eq41284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41284
  have eq42119 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq41269 eq42032
    | exact resolve eq42032 eq41269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41269 eq42032
  have eq42120 : x = y := by grind
  clear eq42119
  have eq42204 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42120
       grind)
    | exact superpose eq42120 eq16
    | exact resolve eq16 eq42120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42206 : x = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq41240
       have i₂ := eq42120
       grind)
    | exact superpose eq42120 eq41240
    | exact resolve eq41240 eq42120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41240 eq42120
  have eq42208 : x = (M.op x x) := by
    first
    | (have j1 := eq10408 x
       grind)
    | (have r₁ := eq42206
       have r₂ := eq10408 x
       grind)
    | exact resolve eq42206 eq10408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10408 eq42206
  have eq42212 : x = (M.op x x) := by grind
  clear eq42208
  have eq42213 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42204
       have i₂ := eq42212
       grind)
    | exact superpose eq42212 eq42204
    | exact resolve eq42204 eq42212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42204
  have eq42214 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq424 x
       have i₂ := eq42212
       grind)
    | exact superpose eq42212 eq424
    | (have j0 := eq424 x
       grind)
    | exact resolve eq424 eq42212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq42284 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq42214
  have eq42354 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42284
       have i₂ := eq42212
       grind)
    | exact superpose eq42212 eq42284
    | exact resolve eq42284 eq42212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42212 eq42284
  have eq42355 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq42354
  have eq42424 : False := by grind
  exact eq42424

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyy_pyx_pxy_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq52 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X4) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X0 x x X4
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op X0 (M.op X3 X4)) X5) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X4)) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op X3 X4)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op X4 X5)) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X3) X4 X5 X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X3 (M.op X0 X3)) ∨ (M.op X3 X3) = X3 ∨ (M.op X3 (M.op X0 X3)) = (k (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X0 X3) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 X3) X3
       grind)
    | (have r₁ := eq12 X3 (M.op X3 X3)
       have r₂ := eq14 X3 X3 X3 X3
       grind)
    | (have r₁ := eq12 (M.op X2 X2) X2
       have r₂ := eq14 X2 X2 X2 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq116 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq116 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq117 (σ X0)
       grind)
    | exact superpose eq117 eq10
    | exact resolve eq10 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq77
    | exact resolve eq77 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq122 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq49
    | exact resolve eq49 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq123 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq122
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq122
    | exact resolve eq122 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq124 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq121
    | exact resolve eq121 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq119
    | exact resolve eq119 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq131 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq105
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq105
    | exact resolve eq105 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq132 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq131
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq131
    | exact resolve eq131 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq173 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq43
  have eq187 : (σ (k (k x x) x)) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq173
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq173
    | exact resolve eq173 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq189 : (k (M.op (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) := by
    first
    | (have i₁ := eq187
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq187
    | exact resolve eq187 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq259 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq117 (τ X0)
       grind)
    | exact superpose eq117 eq34
    | exact resolve eq34 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq328 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq317 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq317
    | exact resolve eq317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq330 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq328 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq328
    | exact resolve eq328 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq328
  have eq444 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq52 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq475 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq259 eq444
    | exact resolve eq444 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq489 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 X1 X2 x y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq678 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X3) ≠ (M.op (M.op X4 X5) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X3) = (k (M.op X4 X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq12 (M.op X1 X2) X0
       have i₂ := eq53 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X5 (M.op (M.op X5 (M.op X3 X4)) X5)
       have r₂ := eq53 X5 (M.op X5 (M.op X3 X4)) X5 X3 X4 X5
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 (M.op X3 X4)) X2) X2
       have r₂ := eq53 X2 (M.op X2 (M.op X3 X4)) X2 X3 X4 X2
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1005 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq489
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq489 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op X4 X5)) = (M.op (M.op X0 (M.op x y)) X3) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq55 X0 x x X3 X4 X5
       have i₂ := eq489 X0 x x
       grind)
    | (have i₁ := eq55 X0 x y X3 X4 X5
       have i₂ := eq489 X0 x x
       grind)
    | exact superpose eq489 eq55
    | (have j0 := eq55 X0 x y X3 X4 X5
       grind)
    | exact resolve eq55 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1085 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op x y)) X3) = (M.op (M.op X0 X3) (M.op x y)) := by
    intro X0 X3
    first
    | (have i₁ := eq1084 X0 X3 x x
       have i₂ := eq489 (M.op X0 X3) x x
       grind)
    | (have i₁ := eq1084 X0 X3 x y
       have i₂ := eq489 (M.op X0 X3) x x
       grind)
    | exact superpose eq489 eq1084
    | (have j0 := eq1084 X0 X3 x y
       grind)
    | exact resolve eq1084 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1472 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X3 (M.op x y)) ∨ (M.op X3 X3) = X3 ∨ (M.op X3 (M.op X0 X3)) = (k (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 X1 X2 X3
       have i₂ := eq489 X3 X0 X3
       grind)
    | (have i₁ := eq113 x X1 X2 y
       have i₂ := eq489 y X1 X2
       grind)
    | exact superpose eq489 eq113
    | (have j0 := eq113 X0 X1 X2 X3
       grind)
    | (have r₁ := eq113 X2 x y X2
       have r₂ := eq489 X2 X2 X2
       grind)
    | exact resolve eq113 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1473 : ∀ X0 X3 : G, (M.op X0 (M.op x y)) ≠ (M.op X3 (M.op x y)) ∨ (M.op X3 X3) = X3 ∨ (M.op X3 (M.op X0 X3)) = (k (M.op X0 X3) X3) := by
    intro X0 X3
    first
    | (have i₁ := eq1472 X0 x x X3
       have i₂ := eq489 X0 x x
       grind)
    | (have i₁ := eq1472 X0 x y X3
       have i₂ := eq489 X0 x x
       grind)
    | exact superpose eq489 eq1472
    | (have j0 := eq1472 X0 x y X3
       grind)
    | (have r₁ := eq1472 X0 x x X0
       have r₂ := eq489 X0 x x
       grind)
    | (have r₁ := eq1472 X0 x y X0
       have r₂ := eq489 X0 x y
       grind)
    | exact resolve eq1472 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1474 : ∀ X0 X3 : G, (M.op X0 (M.op x y)) ≠ (M.op X3 (M.op x y)) ∨ (k (M.op X0 X3) X3) = (M.op X3 (M.op x y)) ∨ (M.op X3 X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq1473 X0 X3
       have i₂ := eq489 X3 X0 X3
       grind)
    | (have i₁ := eq1473 x y
       have i₂ := eq489 y x x
       grind)
    | exact superpose eq489 eq1473
    | (have j0 := eq1473 X0 X3
       grind)
    | (have r₁ := eq1473 X0 X0
       have r₂ := eq489 X0 x y
       grind)
    | exact resolve eq1473 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1538 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1474 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1880 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X0 (σ X1)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1900 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1880 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq1901 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1900 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq1911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1901 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1901
    | (have j0 := eq1901 X0 X1
       grind)
    | exact resolve eq1901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq1912 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1911 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq2014 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq489 X1 (σ X0) (σ X0)
       have i₂ := eq126 X0
       grind)
    | exact superpose eq126 eq489
    | exact resolve eq489 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2554 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (M.op x y)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq126 (M.op X0 X0)
       have i₂ := eq2014 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq2014 eq126
    | exact resolve eq126 eq2014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2559 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (M.op x y)) = (σ (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2554 X0
       have i₂ := eq489 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq489 eq2554
    | exact resolve eq2554 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq11192 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1912 X0 X1
       have i₂ := eq126 X1
       grind)
    | exact superpose eq126 eq1912
    | (have j0 := eq1912 X0 X1
       grind)
    | exact resolve eq1912 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq1912
  have eq11284 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11192 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11192
    | exact resolve eq11192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11361 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq11192 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11192
    | (have j0 := eq11192 X0 y
       grind)
    | exact resolve eq11192 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11192
  have eq11457 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11361 X0
       have i₂ := eq124
       grind)
    | exact superpose eq124 eq11361
    | (have j0 := eq11361 X0
       grind)
    | exact resolve eq11361 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11361
  have eq11463 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11284 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq11284
    | (have j0 := eq11284 X0 X1
       grind)
    | exact resolve eq11284 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq11284
  have eq11502 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11463 X0 X1
       have i₂ := eq330 X0
       grind)
    | exact superpose eq330 eq11463
    | (have j0 := eq11463 X0 X1
       grind)
    | exact resolve eq11463 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq11463
  have eq27793 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11457 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11457
    | (have j0 := eq11457 x
       grind)
    | exact resolve eq11457 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11457
  have eq27844 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq27793
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq27793
    | exact resolve eq27793 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27793
  have eq27872 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq27844
    | exact resolve eq27844 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27844
  have eq28718 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11502 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11502
    | (have j0 := eq11502 X1 X1
       grind)
    | exact resolve eq11502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11502
  have eq29237 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq28718 x y
       grind)
    | exact superpose eq28718 eq44
    | (have j1 := eq28718 x y
       grind)
    | exact resolve eq44 eq28718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq28718
  have eq29426 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq29237
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29237
    | exact resolve eq29237 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29237
  have eq29559 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq29426
    | exact resolve eq29426 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29426
  have eq29659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29559 eq27872
    | exact resolve eq27872 eq29559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27872 eq29559
  have eq29666 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq29659
       have r₂ := eq27
       grind)
    | exact resolve eq29659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29659
  have eq29690 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29666 eq132
    | exact resolve eq132 eq29666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq29666
  have eq29762 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq29690
    | exact resolve eq29690 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29690
  have eq29763 : y = (M.op y y) := by grind
  clear eq29762
  have eq29774 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq29763
       grind)
    | exact superpose eq29763 eq124
    | exact resolve eq124 eq29763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq29805 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq29763
       grind)
    | exact superpose eq29763 eq56
    | exact resolve eq56 eq29763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq29810 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq489 X0 y y
       have i₂ := eq29763
       grind)
    | exact superpose eq29763 eq489
    | exact resolve eq489 eq29763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29763
  have eq29825 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq259 eq29805
    | exact resolve eq29805 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq29805
  have eq29848 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq29774
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29774
    | exact resolve eq29774 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq29774
  have eq29851 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq29825
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29825
    | exact resolve eq29825 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29825
  have eq30097 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq29848 eq57
    | exact resolve eq57 eq29848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq29848
  have eq30114 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq279 eq30097
    | exact resolve eq30097 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq30097
  have eq30141 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq26 eq30114
    | exact resolve eq30114 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30114
  have eq35186 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq30141 eq29810
    | exact resolve eq29810 eq30141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39615 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X0) ≠ (M.op (M.op X0 (M.op X1 X2)) (M.op x y)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X3) = (k (M.op X4 X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq678 X0 X1 X2 X3 X4 X5
       have i₂ := eq1005 (M.op X0 (M.op X1 X2)) X3
       grind)
    | exact superpose eq1005 eq678
    | (have j0 := eq678 X0 X1 X2 X3 X4 X5
       grind)
    | (have r₁ := eq678 (M.op x y) X1 X2 X1 (M.op x y) (M.op X1 X2)
       have r₂ := eq1005 (M.op (M.op x y) (M.op X1 X2)) X1
       grind)
    | (have r₁ := eq678 X1 X1 X2 (M.op x y) (M.op (M.op X1 (M.op X1 X2)) (M.op x y)) X1
       have r₂ := eq1005 (M.op (M.op X1 (M.op X1 X2)) (M.op x y)) X1
       grind)
    | exact resolve eq678 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq39616 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X0) ≠ (M.op (M.op X0 (M.op x y)) (M.op X1 X2)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X3) = (k (M.op X4 X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq39615 X0 x y X3 X4 X5
       have i₂ := eq1085 X0 sF0
       grind)
    | exact superpose eq1085 eq39615
    | (have j0 := eq39615 X0 X1 X2 X3 X4 X5
       grind)
    | (have r₁ := eq39615 (M.op X1 X2) X1 X2 X3 (M.op X1 X2) (M.op x y)
       have r₂ := eq1085 (M.op X1 X2) (M.op X1 X2)
       grind)
    | (have r₁ := eq39615 (M.op x y) x y X3 (M.op x y) (M.op x y)
       have r₂ := eq1085 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq39615 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39615
  have eq39617 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X0) ≠ (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X3) = (k (M.op X4 X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq39616 X0 X1 X2 X3 X4 X5
       have i₂ := eq489 (M.op X0 sF0) X1 X2
       grind)
    | (have i₁ := eq39616 X0 x y X3 X4 X5
       have i₂ := eq489 (M.op X0 sF0) X1 X2
       grind)
    | exact superpose eq489 eq39616
    | (have j0 := eq39616 X0 x y X3 X4 X5
       grind)
    | (have r₁ := eq39616 (M.op X1 X2) x y X3 (M.op X1 X2) (M.op x y)
       have r₂ := eq489 (M.op (M.op X1 X2) (M.op x y)) X1 X2
       grind)
    | (have r₁ := eq39616 (M.op x y) X1 X2 X3 (M.op x y) (M.op x y)
       have r₂ := eq489 (M.op (M.op x y) (M.op x y)) X1 X2
       grind)
    | exact resolve eq39616 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39616
  have eq39618 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op x y)) ≠ (M.op (M.op X4 X5) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X3) = (k (M.op X4 X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq39617 X0 X1 X2 X3 X4 X5
       have i₂ := eq1005 X0 sF0
       grind)
    | exact superpose eq1005 eq39617
    | (have j0 := eq39617 X0 X1 X2 X3 X4 X5
       grind)
    | (have r₁ := eq39617 X1 X1 X2 X3 (M.op X1 (M.op x y)) X1
       have r₂ := eq1005 (M.op X1 (M.op x y)) X1
       grind)
    | (have r₁ := eq39617 (M.op x y) X1 X2 X3 x y
       have r₂ := eq1005 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq39617 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39617
  have eq39619 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X3) = (k (M.op X4 X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq29810 eq39618
    | (have j0 := eq39618 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq39618 eq29810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39618
  have eq39620 : ∀ X0 X1 X2 X4 X5 : G, (k (M.op X4 X5) X0) = (M.op (M.op X0 (M.op X1 X2)) (M.op x y)) ∨ (M.op (M.op X4 X5) X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq39619 X0 X1 X2 x X4 X5
       have i₂ := eq1005 (M.op X0 (M.op X1 X2)) x
       grind)
    | exact superpose eq1005 eq39619
    | (have j0 := eq39619 X0 X1 X2 x X4 X5
       grind)
    | exact resolve eq39619 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39619
  have eq39621 : ∀ X0 X1 X2 X4 X5 : G, (k (M.op X4 X5) X0) = (M.op (M.op X0 (M.op x y)) (M.op X1 X2)) ∨ (M.op (M.op X4 X5) X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq39620 X0 x y X4 X5
       have i₂ := eq1085 X0 sF0
       grind)
    | exact superpose eq1085 eq39620
    | (have j0 := eq39620 X0 X1 X2 X4 X5
       grind)
    | exact resolve eq39620 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085 eq39620
  have eq39622 : ∀ X0 X4 X5 : G, (k (M.op X4 X5) X0) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op (M.op X4 X5) X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = X0 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq39621 X0 x x X4 X5
       have i₂ := eq489 (M.op X0 sF0) x x
       grind)
    | (have i₁ := eq39621 X0 x y X4 X5
       have i₂ := eq489 (M.op X0 sF0) x x
       grind)
    | exact superpose eq489 eq39621
    | (have j0 := eq39621 X0 x y X4 X5
       grind)
    | exact resolve eq39621 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq39621
  have eq39623 : ∀ X0 X4 X5 : G, (M.op X0 (M.op x y)) = (k (M.op X4 X5) X0) ∨ (M.op (M.op X4 X5) X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = X0 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq39622 X0 X4 X5
       have i₂ := eq1005 X0 sF0
       grind)
    | exact superpose eq1005 eq39622
    | (have j0 := eq39622 X0 X4 X5
       grind)
    | exact resolve eq39622 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq39622
  have eq39624 : ∀ X0 X4 X5 : G, (M.op (M.op X4 X5) X0) ≠ (M.op X0 y) ∨ (k (M.op X4 X5) X0) = (M.op X0 y) ∨ (M.op X0 X0) = X0 := by
    intro X0 X4 X5
    first
    | exact superpose eq29810 eq39623
    | (have j0 := eq39623 X0 X4 X5
       grind)
    | (have r₁ := eq39623 (M.op x y) x y
       have r₂ := eq29810 (M.op x y)
       grind)
    | exact resolve eq39623 eq29810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39623
  have eq39754 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op X0 y) ∨ (k (M.op x X0) X0) = (M.op X0 y) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39624 X0 x X0
       have i₂ := eq475 X0
       grind)
    | exact superpose eq475 eq39624
    | (have j0 := eq39624 X0 x X0
       grind)
    | exact resolve eq39624 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq39624
  have eq39863 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (k (M.op x X0) X0) = (M.op X0 y) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq29851 eq39754
    | (have j0 := eq39754 X0
       grind)
    | (have r₁ := eq39754 x
       have r₂ := eq29851
       grind)
    | exact resolve eq39754 eq29851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39754
  have eq52395 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x x) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39863 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39863
    | (have j0 := eq39863 x
       grind)
    | (have r₁ := eq39863 x
       have r₂ := eq18
       grind)
    | exact resolve eq39863 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq39863
  have eq52401 : (M.op x y) = (k (M.op x x) x) ∨ x = (M.op x x) := by grind
  clear eq52395
  have eq306303 : (σ (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq189
       have i₂ := eq52401
       grind)
    | exact superpose eq52401 eq189
    | exact resolve eq189 eq52401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq52401
  have eq306340 : (σ (M.op x y)) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq306303
    | exact resolve eq306303 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306303
  have eq306388 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq306340 eq1538
    | (have j0 := eq1538 (σ x)
       grind)
    | exact resolve eq1538 eq306340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq306340
  have eq306402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30141 eq306388
    | exact resolve eq306388 eq30141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30141 eq306388
  have eq306412 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq306402
       have r₂ := eq27
       grind)
    | exact resolve eq306402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306402
  have eq306421 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq306412 eq123
    | exact resolve eq123 eq306412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq306412
  have eq306569 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq306421
    | exact resolve eq306421 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq306421
  have eq306570 : x = (M.op x x) := by grind
  clear eq306569
  have eq306668 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq2559 x
       have i₂ := eq306570
       grind)
    | exact superpose eq306570 eq2559
    | exact resolve eq2559 eq306570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559 eq306570
  have eq306781 : (σ (M.op x (M.op x y))) = (M.op (σ x) y) := by
    first
    | exact superpose eq29810 eq306668
    | exact resolve eq306668 eq29810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29810 eq306668
  have eq306848 : (σ (M.op x (M.op x y))) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq306781
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq306781
    | exact resolve eq306781 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq306781
  have eq306886 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq35186 eq306848
    | exact resolve eq306848 eq35186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35186 eq306848
  have eq306907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29851 eq306886
    | exact resolve eq306886 eq29851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29851 eq306886
  have eq306916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq306907
    | exact resolve eq306907 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq306907
  have eq306921 : False := by grind
  exact eq306921

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_x_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq25 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X4) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X0 x x X4
       have i₂ := eq9 X0 x x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X1) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 X0 X2 X3 (M.op X4 X5)
       have i₂ := eq9 X0 X4 X5 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X1 X2 x
       have i₂ := eq9 X0 X3 X4 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X0 X1)) = (M.op (M.op X0 X1) X3) ∨ (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq62
    | (have j0 := eq62 (σ X0) (σ X1)
       grind)
    | exact resolve eq62 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (τ X0) (τ X1)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq62
    | (have j0 := eq62 (τ X0) (τ X1)
       grind)
    | exact resolve eq62 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq152 : ∀ X0 X1 X2 X3 X4 : G, (k X4 (M.op X0 X1)) = (M.op (M.op X0 X1) X4) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X4 (M.op X0 X1)
       have i₂ := eq29 (M.op X0 X1) X0 X1 X2 X3
       grind)
    | (have i₁ := eq12 X4 (M.op X0 X1)
       have i₂ := eq29 (M.op X0 X1) X2 X3 X0 X1
       grind)
    | exact superpose eq29 eq12
    | (have j0 := eq12 X4 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq16
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq670 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X3) X3) ∨ (k X2 (σ (M.op X0 X1))) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 X2 (M.op X0 X1)
       have i₂ := eq39 X0 X1 X3 (τ X2)
       grind)
    | exact superpose eq39 eq17
    | (have j1 := eq39 X0 X1 X3 X3
       grind)
    | exact resolve eq17 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq39
  have eq849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq584
       have i₂ := eq62 y x
       grind)
    | exact superpose eq62 eq584
    | (have j1 := eq62 (σ y) (σ x)
       grind)
    | exact resolve eq584 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq852 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq849
  have eq853 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1 y
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq9
    | exact resolve eq9 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1034 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 (M.op X3 X4)) ∨ (k X5 (σ (M.op X0 (M.op X3 X4)))) = (σ (M.op (M.op X0 (M.op X3 X4)) (τ X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq670 X0 (M.op X3 X4) X5 (M.op X3 X4)
       have i₂ := eq27 X0 (M.op X3 X4) X1 X2 X3 X4
       grind)
    | exact superpose eq27 eq670
    | (have j0 := eq670 X0 (M.op X3 X4) X5 X3
       grind)
    | (have r₁ := eq670 X0 (M.op X4 X5) X2 (M.op X4 X5)
       have r₂ := eq27 X0 (M.op X4 X5) X4 X5 X4 X5
       grind)
    | exact resolve eq670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq670
  have eq1041 : ∀ X0 X3 X4 X5 : G, (k X5 (σ (M.op X0 (M.op X3 X4)))) = (σ (M.op (M.op X0 (M.op X3 X4)) (τ X5))) := by
    intro X0 X3 X4 X5
    first
    | (have j0 := eq1034 X0 x x X3 X4 X5
       grind)
    | (have r₁ := eq1034 X0 x x X3 X4 X5
       have r₂ := eq29 X0 x x X3 X4
       grind)
    | (have r₁ := eq1034 X0 X3 X4 x x X5
       have r₂ := eq29 X0 x x X3 X4
       grind)
    | exact resolve eq1034 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1034
  have eq2173 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq853 X0 X1
       grind)
    | exact superpose eq853 eq16
    | (have j1 := eq853 X0 X1
       grind)
    | exact resolve eq16 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq2201 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ x = (M.op x (M.op X0 X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2173 X0 X1
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq2173
    | exact resolve eq2173 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2202 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq3739 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (τ X0)) = (τ (k X0 (σ (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (M.op (M.op X1 (M.op X2 X3)) (τ X0))
       have i₂ := eq1041 X1 X2 X3 X0
       grind)
    | exact superpose eq1041 eq10
    | exact resolve eq10 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq3758 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (τ X0)) = (k (τ X0) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3739 X0 X1 X2 X3
       have i₂ := eq22 X0 (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq22 eq3739
    | exact resolve eq3739 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3739
  have eq4133 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (k X0 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3758 (σ X0) X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3758
    | exact resolve eq3758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758
  have eq4254 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 X1) X1) X4) = (k X4 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq4133 X0 X0 X1 x
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq4133
    | exact resolve eq4133 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133
  have eq5385 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq74 X0 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq74 X0 X0
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq5441 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq5385 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq5385 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq5385 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5385
  have eq69791 : ∀ X0 X1 X2 : G, (M.op x X0) = (k X0 x) ∨ x ≠ (M.op x (M.op X1 X2)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 x y X2 x x
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq152
    | exact resolve eq152 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq852
  have eq69847 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq69791 X0 x x
       grind)
    | (have r₁ := eq69791 X0 X0 x
       have r₂ := eq2202 X0 x
       grind)
    | exact resolve eq69791 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202 eq69791
  have eq69889 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq584
       have i₂ := eq69847 y
       grind)
    | exact superpose eq69847 eq584
    | exact resolve eq584 eq69847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq69847
  have eq69890 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq69889
  have eq69891 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq69890
  have eq69901 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ x) X0 X1 (σ y)
       have i₂ := eq69891
       grind)
    | exact superpose eq69891 eq9
    | exact resolve eq9 eq69891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69904 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (σ x) X0 (σ y)
       have i₂ := eq69891
       grind)
    | exact superpose eq69891 eq25
    | exact resolve eq25 eq69891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq70031 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq4254 (σ x) (σ y) x
       have i₂ := eq69891
       grind)
    | exact superpose eq69891 eq4254
    | exact resolve eq4254 eq69891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254
  have eq70083 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq70031 X0
       have i₂ := eq69891
       grind)
    | exact superpose eq69891 eq70031
    | exact resolve eq70031 eq69891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70031
  have eq70104 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq69904 X0
       have i₂ := eq69891
       grind)
    | exact superpose eq69891 eq69904
    | exact resolve eq69904 eq69891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69904
  have eq70107 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq69901 X0 X1
       have i₂ := eq69891
       grind)
    | exact superpose eq69891 eq69901
    | exact resolve eq69901 eq69891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69891 eq69901
  have eq71390 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70107 (M.op (σ x) x) x
       have i₂ := eq70104 x
       grind)
    | exact superpose eq70104 eq70107
    | exact resolve eq70107 eq70104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70104 eq70107
  have eq79581 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq70083 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq70083
    | exact resolve eq70083 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79590 : ∀ X0 : G, (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq5441 (σ x) X0
       have i₂ := eq70083 (σ x)
       grind)
    | exact superpose eq70083 eq5441
    | (have j0 := eq5441 (σ x) X0
       grind)
    | exact resolve eq5441 eq70083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5441 eq70083
  have eq79618 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq79590 X0
       have i₂ := eq71390
       grind)
    | exact superpose eq71390 eq79590
    | (have j0 := eq79590 X0
       grind)
    | exact resolve eq79590 eq71390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71390 eq79590
  have eq79619 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op (τ (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq79618 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79618
  have eq79626 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq79619 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq79619
    | exact resolve eq79619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79619
  have eq128189 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq79581 X0
       have i₂ := eq79626 X0
       grind)
    | exact superpose eq79626 eq79581
    | exact resolve eq79581 eq79626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79581 eq79626
  have eq128557 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128189 y
       grind)
    | exact superpose eq128189 eq16
    | (have r₁ := eq16
       have r₂ := eq128189 y
       grind)
    | exact resolve eq16 eq128189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128189
  have eq128868 : False := by grind
  exact eq128868
