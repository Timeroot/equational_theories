import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pxx_pxy_Equation1924 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X1 X0)) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq273 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq273 (σ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq349 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq351 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq349 X0 X1
       have j1 := eq350 X0 X1
       grind)
    | (have r₁ := eq349 X0 X1
       have r₂ := eq350 X0 X1
       grind)
    | exact resolve eq349 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq350
  have eq415 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq351 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq351
    | exact resolve eq351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq456 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq61
    | (have j1 := eq415 X0 (M.op (M.op X1 X0) X0)
       grind)
    | exact resolve eq61 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq457 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq9
    | (have j1 := eq415 X0 (M.op X1 X0)
       grind)
    | exact resolve eq9 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq749 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq457 X0 X1
       grind)
    | exact superpose eq457 eq456
    | (have j0 := eq456 X0 X1
       have j1 := eq457 X0 X1
       grind)
    | exact resolve eq456 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq457
  have eq765 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq749 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq770 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq765 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq765 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq765 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq794 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq770 (σ X1) (σ X0)
       grind)
    | exact superpose eq770 eq15
    | exact resolve eq15 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq794 X0 X1
       have i₂ := eq770 X1 X0
       grind)
    | exact superpose eq770 eq794
    | exact resolve eq794 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq794
  have eq1154 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq821 x y
       grind)
    | exact superpose eq821 eq16
    | (have r₁ := eq16
       have r₂ := eq821 x y
       grind)
    | exact resolve eq16 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq1176 : False := by grind
  exact eq1176

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyx_pxy_Equation1924 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1924 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq270 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq270 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq270 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq282 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq271 (τ X0)
       grind)
    | exact superpose eq271 eq31
    | exact resolve eq31 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq295 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq288 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq288
    | exact resolve eq288 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq282
    | exact resolve eq282 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq282
  have eq346 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq9
    | exact resolve eq9 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (σ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq442 X0 X1
       have j1 := eq348 X0 X1
       grind)
    | (have r₁ := eq442 X0 X1
       have r₂ := eq348 X0 X1
       grind)
    | exact resolve eq442 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq442
  have eq470 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq467 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq467
    | exact resolve eq467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq467 X1 (σ X0)
       grind)
    | exact superpose eq467 eq15
    | (have j1 := eq467 X1 (σ X0)
       grind)
    | exact resolve eq15 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq501 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq470
    | (have j0 := eq470 X0 X1
       grind)
    | exact resolve eq470 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq470
  have eq502 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq501
    | (have j0 := eq501 X0 X1
       grind)
    | exact resolve eq501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq525 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq502 X1 (τ X0)
       grind)
    | exact superpose eq502 eq17
    | (have j1 := eq502 X1 (τ X0)
       grind)
    | exact resolve eq17 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq502
  have eq633 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq525 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq525
    | exact resolve eq525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq671 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq3708 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq481 x y
       grind)
    | exact superpose eq481 eq16
    | (have j1 := eq481 x y
       grind)
    | exact resolve eq16 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq3766 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq3708
       have i₂ := eq671 x y
       grind)
    | exact superpose eq671 eq3708
    | (have j1 := eq671 x y
       grind)
    | (have r₁ := eq3708
       have r₂ := eq671 x y
       grind)
    | exact resolve eq3708 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq3708
  have eq3767 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq3766
  have eq3777 : (σ x) = (M.op (M.op (σ y) (σ (M.op y y))) (σ (M.op y y))) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq3767
       grind)
    | exact superpose eq3767 eq9
    | exact resolve eq9 eq3767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3767
  have eq3778 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3777
       have i₂ := eq346 y
       grind)
    | exact superpose eq346 eq3777
    | exact resolve eq3777 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq3777
  have eq3802 : y = (M.op (M.op y (M.op y x)) (M.op y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq3778
       grind)
    | exact superpose eq3778 eq9
    | exact resolve eq9 eq3778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3778
  have eq3804 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3802
       have i₂ := eq9 x y
       grind)
    | exact superpose eq9 eq3802
    | exact resolve eq3802 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802
  have eq3808 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3804
       grind)
    | exact superpose eq3804 eq16
    | exact resolve eq16 eq3804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3804
  have eq3809 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3808
       have r₂ := eq301 x
       grind)
    | exact resolve eq3808 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq3811 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3809
       grind)
    | exact superpose eq3809 eq16
    | exact resolve eq16 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3812 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3809
       grind)
    | exact superpose eq3809 eq10
    | exact resolve eq10 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809
  have eq3859 : x = y := by
    first
    | (have i₁ := eq3812
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3812
    | exact resolve eq3812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3812
  have eq3860 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3811
       have i₂ := eq301 x
       grind)
    | exact superpose eq301 eq3811
    | exact resolve eq3811 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq3811
  have eq3862 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3860
       have i₂ := eq3859
       grind)
    | exact superpose eq3859 eq3860
    | exact resolve eq3860 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859 eq3860
  have eq3863 : False := by grind
  exact eq3863

/-- `Equation1924`: `x = (y ◇ (y ◇ x)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyy_pyx_Equation1924 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1924 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1924.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : y = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq94 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq90
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq94
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq115
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq115
    | exact resolve eq115 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq318 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq3911 : ∀ X0 : G, (σ y) = (M.op (M.op (σ X0) (σ (k y X0))) (σ (k y X0))) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq92 eq14
    | (have j1 := eq92 X0
       grind)
    | exact resolve eq14 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq9842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9842
    | exact resolve eq9842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9842
  have eq9854 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq9843
       have r₂ := eq28
       grind)
    | exact resolve eq9843 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9843
  have eq9858 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9854
    | exact resolve eq9854 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9854
  have eq9870 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9858 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9858
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9858
       grind)
    | exact resolve eq12 eq9858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9858
  have eq37531 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq9870
    | (have j0 := eq9870 (σ x)
       grind)
    | (have r₁ := eq9870 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq9870 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9870
  have eq37532 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq37531
  have eq37533 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq37532
  have eq37551 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq37533 eq116
    | exact resolve eq116 eq37533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq37533
  have eq37568 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq37551
  have eq37589 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq37568 eq75
    | exact resolve eq75 eq37568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37568
  have eq37615 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq37589
    | exact resolve eq37589 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq37589
  have eq38001 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq37615
       grind)
    | exact superpose eq37615 eq95
    | exact resolve eq95 eq37615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq38012 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op X0 X0) = (k y X0) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq37615
       grind)
    | exact superpose eq37615 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq37615
       grind)
    | exact resolve eq12 eq37615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37615
  have eq38039 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq38001
    | exact resolve eq38001 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38001
  have eq524541 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq38012 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38012
    | (have j0 := eq38012 x
       grind)
    | (have r₁ := eq38012 x
       have r₂ := eq19
       grind)
    | exact resolve eq38012 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38012
  have eq524542 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq524541
  have eq524543 : (M.op x x) = (k y x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq524542
  have eq526320 : (σ y) = (M.op (M.op (σ x) (σ (M.op x x))) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3911 x
       have i₂ := eq524543
       grind)
    | exact superpose eq524543 eq3911
    | (have j0 := eq3911 x
       grind)
    | exact resolve eq3911 eq524543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3911 eq524543
  have eq526412 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq526320
       have i₂ := eq318 x
       grind)
    | exact superpose eq318 eq526320
    | exact resolve eq526320 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq526320
  have eq526413 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq526412
  have eq526444 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq526413
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq526413
    | exact resolve eq526413 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526413
  have eq526445 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq526444
  have eq526461 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq526445
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq526445
    | exact resolve eq526445 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526445
  have eq526475 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq526461
    | exact resolve eq526461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526461
  have eq526577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq526475 eq38039
    | exact resolve eq38039 eq526475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38039 eq526475
  have eq526836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq526577
  have eq526894 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq526836
       have r₂ := eq28
       grind)
    | exact resolve eq526836 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526836
  have eq526968 : x = (M.op (M.op x (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq526894
       grind)
    | exact superpose eq526894 eq14
    | exact resolve eq14 eq526894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526894
  have eq527028 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq53 eq526968
    | exact resolve eq526968 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq526968
  have eq527029 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq527028
  have eq527069 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq527029 eq30
    | exact resolve eq30 eq527029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq527029
  have eq527234 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq527069
    | exact resolve eq527069 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq527069
  have eq527235 : x = y := by grind
  clear eq527234
  have eq527258 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq527235
       grind)
    | exact superpose eq527235 eq19
    | exact resolve eq19 eq527235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq527259 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq527235
       grind)
    | exact superpose eq527235 eq25
    | exact resolve eq25 eq527235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq527235
  have eq527597 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq527259
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq527259
    | exact resolve eq527259 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq527259
  have eq527626 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq527597 eq27
    | exact resolve eq27 eq527597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq527597
  have eq527967 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq527626 eq75
    | exact resolve eq75 eq527626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq527626
  have eq528140 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq527967
       have i₂ := eq527258
       grind)
    | exact superpose eq527258 eq527967
    | exact resolve eq527967 eq527258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527258 eq527967
  have eq528173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq528140 eq15
    | exact resolve eq15 eq528140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528140
  have eq528724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq528173
    | exact resolve eq528173 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq528173
  have eq528869 : False := by grind
  exact eq528869

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_pyy_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 (k X1 X1) X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq46 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq51
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq58 X1 X0
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq58 X0 (M.op X1 X1)
       have r₂ := eq47 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq58 X1 X1
       have r₂ := eq47 (k X1 X1) X1
       grind)
    | exact resolve eq58 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq58
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq64 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq64 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq64
  have eq138 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq142 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq138 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq138 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | exact resolve eq138 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq138
  have eq397 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq142 (σ X0) (σ X1)
       grind)
    | exact superpose eq142 eq15
    | exact resolve eq15 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 X1
       have i₂ := eq142 X0 X1
       grind)
    | exact superpose eq142 eq397
    | exact resolve eq397 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq397
  have eq404 : False := by grind
  exact eq404

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq516 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq506 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq522 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq516 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq516 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq516 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq516 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq523 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq505 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq505 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq505 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq522
    | (have j0 := eq522 X0 X1
       grind)
    | exact resolve eq522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq532 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq531 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq533 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq523
    | (have j0 := eq523 X0 X1
       grind)
    | exact resolve eq523 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq534 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq539 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq534 X0 X1
       have j1 := eq532 X0 X1
       grind)
    | (have r₁ := eq534 X0 X1
       have r₂ := eq532 X0 X1
       grind)
    | exact resolve eq534 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq534
  have eq540 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq539
    | exact resolve eq539 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq539 x y
       grind)
    | exact superpose eq539 eq16
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq671 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq540 X0 (τ X1)
       grind)
    | exact superpose eq540 eq18
    | exact resolve eq18 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq540
  have eq684 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq671
    | exact resolve eq671 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq690 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq684
    | exact resolve eq684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq702 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq551
       have i₂ := eq690 x y
       grind)
    | exact superpose eq690 eq551
    | exact resolve eq551 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq690
  have eq703 : False := by grind
  exact eq703

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X1)) X0
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq187 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (M.op (σ X0) (M.op X2 X2)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq9
    | (have j1 := eq80 X0 X1
       grind)
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1150 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq196 (τ X0) (τ X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq196
    | (have j0 := eq196 (τ X0) (τ X1)
       grind)
    | exact resolve eq196 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1163 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1150 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1150
    | (have j0 := eq1150 X0 X1
       grind)
    | exact resolve eq1150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1168 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1163 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1163
    | (have j0 := eq1163 X0 X1
       grind)
    | exact resolve eq1163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1172 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1168 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1168
    | (have j0 := eq1168 X0 X1
       grind)
    | exact resolve eq1168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1175 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1172 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1172
    | (have j0 := eq1172 X0 X1
       grind)
    | exact resolve eq1172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1178 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1175
    | (have j0 := eq1175 X0 X1
       grind)
    | exact resolve eq1175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1179 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1178 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1178
    | (have j0 := eq1178 X0 X1
       grind)
    | exact resolve eq1178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq2083 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (M.op (σ X0) (M.op X1 X1)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq2084 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op (σ X0) (M.op X1 X1)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq4075 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 (M.op X1 X1)) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2084 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2084
    | exact resolve eq2084 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq4124 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4075 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq4075
    | (have j0 := eq4075 X0 X1
       grind)
    | exact resolve eq4075 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq4125 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4124 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4124
    | (have j0 := eq4124 X0 X1
       grind)
    | exact resolve eq4124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4156 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq21 X0 x (k X0 X0)
       have i₂ := eq4125 X0 x
       grind)
    | exact superpose eq4125 eq21
    | (have j1 := eq4125 X0 x
       grind)
    | exact resolve eq21 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq4125
  have eq4195 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq4156
  have eq4245 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4195
  have eq4340 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq79 (σ X1) X1
       grind)
    | (have r₁ := eq13 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq79 (M.op (M.op (σ X1) (σ X1)) X1) X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq4355 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4340
  have eq4356 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4355 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4355
  have eq4471 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4245 (σ X0)
       grind)
    | exact superpose eq4245 eq15
    | exact resolve eq15 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4479 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq4245 (τ X0)
       grind)
    | exact superpose eq4245 eq37
    | exact resolve eq37 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4530 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4479 X0
       have i₂ := eq4245 X0
       grind)
    | exact superpose eq4245 eq4479
    | exact resolve eq4479 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479
  have eq4537 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4471 X0
       have i₂ := eq4245 X0
       grind)
    | exact superpose eq4245 eq4471
    | exact resolve eq4471 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4245 eq4471
  have eq4985 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5015 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4985 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq4985
    | exact resolve eq4985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4985
  have eq5037 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5015
  have eq1334579 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4356 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4356
    | exact resolve eq4356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334794 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X1)
       have i₂ := eq4356 (σ X0) X1
       grind)
    | exact superpose eq4356 eq32
    | (have j1 := eq4356 (σ X0) X1
       grind)
    | exact resolve eq32 eq4356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4356
  have eq1335008 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1334794 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1334794
    | (have j0 := eq1334794 X0 X1
       grind)
    | exact resolve eq1334794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334794
  have eq1335171 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1334579 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq1334579
    | (have j0 := eq1334579 X0 X1
       grind)
    | exact resolve eq1334579 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334579
  have eq1335241 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1335008 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1335008
    | (have j0 := eq1335008 X0 X1
       grind)
    | exact resolve eq1335008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335008
  have eq1335428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1335241 X0 X1
       have i₂ := eq4537 X1
       grind)
    | exact superpose eq4537 eq1335241
    | (have j0 := eq1335241 X0 X1
       grind)
    | exact resolve eq1335241 eq4537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335241
  have eq1335574 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1335428 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1335428
    | (have j0 := eq1335428 X0 X1
       grind)
    | exact resolve eq1335428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335428
  have eq1336143 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq1335171 X1 X0
       grind)
    | exact superpose eq1335171 eq11
    | (have j1 := eq1335171 X1 X0
       grind)
    | exact resolve eq11 eq1335171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335171
  have eq1336446 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1336143 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq1336143
    | (have j0 := eq1336143 X0 X1
       grind)
    | exact resolve eq1336143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336143
  have eq1336816 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1336446 X0 (τ X1)
       grind)
    | exact superpose eq1336446 eq19
    | (have j1 := eq1336446 X0 (τ X1)
       grind)
    | exact resolve eq19 eq1336446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1336446
  have eq1337247 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1336816 X0 X1
       have i₂ := eq4530 X1
       grind)
    | exact superpose eq4530 eq1336816
    | (have j0 := eq1336816 X0 X1
       grind)
    | exact resolve eq1336816 eq4530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336816
  have eq1339266 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1335574 (τ X1) (τ X0)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq1335574
    | (have j0 := eq1335574 (τ X0) (τ X1)
       grind)
    | exact resolve eq1335574 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335574
  have eq1339992 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1339266 X0 X1
       have i₂ := eq4530 X1
       grind)
    | exact superpose eq4530 eq1339266
    | (have j0 := eq1339266 X0 X1
       grind)
    | exact resolve eq1339266 eq4530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339266
  have eq1340306 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1339992 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq1339992
    | (have j0 := eq1339992 X0 X1
       grind)
    | exact resolve eq1339992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339992
  have eq1340556 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1340306 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1340306
    | (have j0 := eq1340306 X0 X1
       grind)
    | exact resolve eq1340306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340306
  have eq1340747 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1340556 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1340556
    | (have j0 := eq1340556 X0 X1
       grind)
    | exact resolve eq1340556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340556
  have eq1340871 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1340747 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1340747
    | (have j0 := eq1340747 X0 X1
       grind)
    | exact resolve eq1340747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340747
  have eq1341406 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1340871 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340871
  have eq1342315 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1341406 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1341406
    | (have j0 := eq1341406 (σ X0) (σ X1)
       grind)
    | exact resolve eq1341406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342367 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq1341406 X0 X1
       grind)
    | exact superpose eq1341406 eq11
    | (have j1 := eq1341406 X0 X1
       grind)
    | exact resolve eq11 eq1341406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341406
  have eq1342679 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1342367 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1342367
    | (have j0 := eq1342367 X0 X1
       grind)
    | exact resolve eq1342367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342367
  have eq1342712 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1342315 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1342315
    | (have j0 := eq1342315 X0 X1
       grind)
    | exact resolve eq1342315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342315
  have eq1342784 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1342712 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1342712
    | (have j0 := eq1342712 X0 X1
       grind)
    | exact resolve eq1342712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342712
  have eq1342830 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1342784 X0 X1
       have i₂ := eq4537 X1
       grind)
    | exact superpose eq4537 eq1342784
    | (have j0 := eq1342784 X0 X1
       grind)
    | exact resolve eq1342784 eq4537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342784
  have eq1342866 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X1))) ≠ X0 ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1342830 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1342830
    | (have j0 := eq1342830 X0 X1
       grind)
    | exact resolve eq1342830 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342830
  have eq1343092 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1179 X0 X1
       have i₂ := eq1342679 X0 X1
       grind)
    | exact superpose eq1342679 eq1179
    | (have j0 := eq1179 X0 X1
       have j1 := eq1342679 X0 X1
       grind)
    | (have r₁ := eq1179 X0 X1
       have r₂ := eq1342679 X0 X1
       grind)
    | (have r₁ := eq1179 (M.op X1 X1) X1
       have r₂ := eq1342679 (k (M.op X1 X1) X1) X1
       grind)
    | exact resolve eq1179 eq1342679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq1342679
  have eq1343393 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1343092 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343092
  have eq1343394 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1343393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343393
  have eq1357461 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1343394 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq1343394
    | (have j0 := eq1343394 (σ X0) (σ X1)
       have j1 := eq80 X0 X1
       grind)
    | exact resolve eq1343394 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1343394
  have eq1357539 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1357461 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357461
  have eq1357607 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1357539 X0 X1
       have j1 := eq196 X0 X1
       grind)
    | (have r₁ := eq1357539 X0 X1
       have r₂ := eq196 X0 X1
       grind)
    | exact resolve eq1357539 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq1357539
  have eq1357728 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1357607 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1357607
    | (have j0 := eq1357607 X0 X1
       grind)
    | exact resolve eq1357607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357607
  have eq1357813 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1357728 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1357728
    | (have j0 := eq1357728 X0 X1
       grind)
    | exact resolve eq1357728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357728
  have eq1357864 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1357813 X0 X1
       have i₂ := eq4537 X1
       grind)
    | exact superpose eq4537 eq1357813
    | (have j0 := eq1357813 X0 X1
       grind)
    | exact resolve eq1357813 eq4537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357813
  have eq1372377 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1357864 (τ X0) (τ X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq1357864
    | (have j0 := eq1357864 (τ X0) (τ X1)
       grind)
    | exact resolve eq1357864 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1372432 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1372377 X0 X1
       have i₂ := eq4530 X1
       grind)
    | exact superpose eq4530 eq1372377
    | (have j0 := eq1372377 X0 X1
       grind)
    | exact resolve eq1372377 eq4530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4530 eq1372377
  have eq1372474 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1372432 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq1372432
    | (have j0 := eq1372432 X0 X1
       grind)
    | exact resolve eq1372432 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372432
  have eq1372503 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1372474 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1372474
    | (have j0 := eq1372474 X0 X1
       grind)
    | exact resolve eq1372474 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372474
  have eq1372526 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) = X0 ∨ (τ X0) ≠ (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1372503 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1372503
    | (have j0 := eq1372503 X0 X1
       grind)
    | exact resolve eq1372503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372503
  have eq1372546 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1372526 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1372526
    | (have j0 := eq1372526 X0 X1
       grind)
    | exact resolve eq1372526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372526
  have eq1455317 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1337247 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1337247
    | (have j0 := eq1337247 X1 (σ X0)
       grind)
    | exact resolve eq1337247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337247
  have eq1455869 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (τ (M.op (σ X0) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1455317 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1455317
    | (have j0 := eq1455317 X0 X1
       grind)
    | exact resolve eq1455317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455317
  have eq1456038 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1455869 X0 X1
       have i₂ := eq4537 X0
       grind)
    | exact superpose eq4537 eq1455869
    | (have j0 := eq1455869 X0 X1
       grind)
    | exact resolve eq1455869 eq4537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455869
  have eq1456178 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1456038 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1456038
    | (have j0 := eq1456038 X0 X1
       grind)
    | exact resolve eq1456038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456038
  have eq1456997 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq187
       have i₂ := eq1456178 y x
       grind)
    | exact superpose eq1456178 eq187
    | (have j1 := eq1456178 y x
       grind)
    | (have r₁ := eq187
       have r₂ := eq1456178 y x
       grind)
    | exact resolve eq187 eq1456178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq1456178
  have eq1457249 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq1456997
  have eq1457428 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1457249
       have i₂ := eq4537 y
       grind)
    | exact superpose eq4537 eq1457249
    | exact resolve eq1457249 eq4537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4537 eq1457249
  have eq1457635 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq1357864 x y
       grind)
    | (have r₁ := eq1457428
       have r₂ := eq1357864 x y
       grind)
    | exact resolve eq1457428 eq1357864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357864 eq1457428
  have eq1459515 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1457635
       grind)
    | exact superpose eq1457635 eq16
    | exact resolve eq16 eq1457635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1459516 : x ≠ (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1342866 x y
       have i₂ := eq1457635
       grind)
    | exact superpose eq1457635 eq1342866
    | (have j0 := eq1342866 x y
       grind)
    | exact resolve eq1342866 eq1457635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342866 eq1457635
  have eq1459553 : x ≠ (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq1459516
  have eq1459567 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1459553
       have r₂ := eq10 x
       grind)
    | exact resolve eq1459553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459553
  have eq1459611 : (τ x) ≠ (τ x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1372546 x y
       have i₂ := eq1459567
       grind)
    | exact superpose eq1459567 eq1372546
    | (have j0 := eq1372546 x y
       grind)
    | exact resolve eq1372546 eq1459567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372546 eq1459567
  have eq1459618 : (τ x) ≠ (τ x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1459611
  have eq1459619 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1459618
  have eq1469987 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1459515
       have i₂ := eq1459619
       grind)
    | exact superpose eq1459619 eq1459515
    | exact resolve eq1459515 eq1459619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459515 eq1459619
  have eq1469988 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1469987
  have eq1469989 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1469988
  have eq1470260 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1469989
       grind)
    | exact superpose eq1469989 eq10
    | exact resolve eq10 eq1469989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469989
  have eq1470691 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1470260
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1470260
    | exact resolve eq1470260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470260
  have eq1470692 : x = (M.op y y) := by grind
  clear eq1470691
  have eq1472068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5037 y
       have i₂ := eq1470692
       grind)
    | exact superpose eq1470692 eq5037
    | exact resolve eq5037 eq1470692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5037 eq1470692
  have eq1472811 : False := by grind
  exact eq1472811

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq80 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq188 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq75 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq75 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq203 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq3509 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq76 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq3510 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq3509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3509
  have eq3515 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3510 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3510
    | (have j0 := eq3510 X0
       grind)
    | exact resolve eq3510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq3527 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3515 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3515
    | exact resolve eq3515 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3515
  have eq3568 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3527 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq3527
    | (have j0 := eq3527 X0
       grind)
    | exact resolve eq3527 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3527
  have eq3585 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3568 X0
       grind)
    | exact superpose eq3568 eq11
    | (have j1 := eq3568 X0
       grind)
    | exact resolve eq11 eq3568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq3680 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3585 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3585
    | (have j0 := eq3585 X0
       grind)
    | exact resolve eq3585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585
  have eq3694 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3680 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq3680 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq3680 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3680
  have eq3795 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq3694 X0
       grind)
    | exact superpose eq3694 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq3694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq3831 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3694 (σ X0)
       grind)
    | exact superpose eq3694 eq15
    | exact resolve eq15 eq3694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3893 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3831 X0
       have i₂ := eq3694 X0
       grind)
    | exact superpose eq3694 eq3831
    | exact resolve eq3831 eq3694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3694 eq3831
  have eq4187 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X1 X0
       have i₂ := eq3893 X0
       grind)
    | exact superpose eq3893 eq80
    | (have j0 := eq80 X1 X0
       grind)
    | exact resolve eq80 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq998176 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq4187 X1 X0
       grind)
    | exact superpose eq4187 eq11
    | (have j1 := eq4187 X1 X0
       grind)
    | exact resolve eq11 eq4187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4187
  have eq998354 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq998176 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq998176
    | (have j0 := eq998176 X0 X1
       grind)
    | exact resolve eq998176 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq998176
  have eq998711 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq998354 X0 X1
       have j1 := eq3795 X1 X0
       grind)
    | (have r₁ := eq998354 X0 X0
       have r₂ := eq3795 X0 X1
       grind)
    | exact resolve eq998354 eq3795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998354
  have eq999785 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq998711 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq998711
    | exact resolve eq998711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999969 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq998711 (σ X0) X1
       grind)
    | exact superpose eq998711 eq15
    | (have j1 := eq998711 (σ X0) X1
       grind)
    | exact resolve eq15 eq998711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998711
  have eq1000495 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq999785 (τ X1) X0
       grind)
    | exact superpose eq999785 eq18
    | (have j1 := eq999785 (τ X1) X0
       grind)
    | exact resolve eq18 eq999785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq999785
  have eq1003905 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1000495 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1000495
    | exact resolve eq1000495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000495
  have eq1005127 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1003905 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1003905
    | (have j0 := eq1003905 X0 X1
       grind)
    | exact resolve eq1003905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003905
  have eq1010017 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq999969 x y
       grind)
    | exact superpose eq999969 eq16
    | (have j1 := eq999969 x y
       grind)
    | exact resolve eq16 eq999969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010860 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq999969 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999969
  have eq1016904 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1010017
       have i₂ := eq1005127 y x
       grind)
    | exact superpose eq1005127 eq1010017
    | (have j1 := eq1005127 (σ y) (σ x)
       grind)
    | (have r₁ := eq1010017
       have r₂ := eq1005127 y x
       grind)
    | exact resolve eq1010017 eq1005127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010017
  have eq1016907 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1016904
  have eq1016913 : x ≠ x ∨ x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1016907
       grind)
    | exact superpose eq1016907 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1016907
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1016907
       grind)
    | exact resolve eq13 eq1016907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016907
  have eq1016940 : x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1016913
  have eq1074147 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1010860 x y
       have i₂ := eq1016940
       grind)
    | exact superpose eq1016940 eq1010860
    | (have j0 := eq1010860 x y
       grind)
    | exact resolve eq1010860 eq1016940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010860 eq1016940
  have eq1074156 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1074147
  have eq1074157 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1074156
  have eq1074206 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1074157
       grind)
    | exact superpose eq1074157 eq16
    | exact resolve eq16 eq1074157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074223 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1074157
       grind)
    | exact superpose eq1074157 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1074157
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1074157
       grind)
    | exact resolve eq13 eq1074157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074157
  have eq1074250 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1074223
  have eq1074255 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1074250
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1074250
    | exact resolve eq1074250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074250
  have eq1074271 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1074255
       have i₂ := eq3893 y
       grind)
    | exact superpose eq3893 eq1074255
    | exact resolve eq1074255 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893 eq1074255
  have eq1143655 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1005127 y x
       have i₂ := eq1074271
       grind)
    | exact superpose eq1074271 eq1005127
    | (have j0 := eq1005127 y x
       grind)
    | exact resolve eq1005127 eq1074271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005127 eq1074271
  have eq1144079 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1143655
       have r₂ := eq1074206
       grind)
    | exact resolve eq1143655 eq1074206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143655
  have eq1147977 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1074206
       have i₂ := eq1144079
       grind)
    | exact superpose eq1144079 eq1074206
    | exact resolve eq1074206 eq1144079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074206 eq1144079
  have eq1148013 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq1147977
  have eq1148014 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1148013
  have eq1148279 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1148014
       grind)
    | exact superpose eq1148014 eq10
    | exact resolve eq10 eq1148014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148014
  have eq1148704 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1148279
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1148279
    | exact resolve eq1148279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148279
  have eq1148705 : y = (M.op y y) := by grind
  clear eq1148704
  have eq1149421 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq1148705
       grind)
    | exact superpose eq1148705 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq1148705
       grind)
    | exact resolve eq12 eq1148705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149481 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3795 y X0
       have i₂ := eq1148705
       grind)
    | exact superpose eq1148705 eq3795
    | (have j0 := eq3795 y X0
       grind)
    | exact resolve eq3795 eq1148705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3795 eq1148705
  have eq1150066 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1149481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149481
  have eq1150067 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1149421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149421
  have eq1170068 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1150066 (σ X0)
       grind)
    | exact superpose eq1150066 eq15
    | exact resolve eq15 eq1150066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150066
  have eq1170292 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1170068 X0
       have i₂ := eq1150067 X0
       grind)
    | exact superpose eq1150067 eq1170068
    | exact resolve eq1170068 eq1150067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150067 eq1170068
  have eq1220432 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1170292 x
       grind)
    | exact superpose eq1170292 eq16
    | (have r₁ := eq16
       have r₂ := eq1170292 x
       grind)
    | exact resolve eq16 eq1170292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170292
  have eq1221188 : False := by grind
  exact eq1221188

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pxx_pyy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq91 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq100 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq109 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq109 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq10
    | exact resolve eq10 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq74
    | exact resolve eq74 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq115 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq110 sF2
       grind)
    | exact superpose eq110 eq49
    | exact resolve eq49 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq116 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq115
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq115
    | exact resolve eq115 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq112
    | exact resolve eq112 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq126 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq100
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq100
    | exact resolve eq100 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq126
    | exact resolve eq126 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq126
  have eq252 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq256 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq663 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X0 X0) X1 X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y) X0
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq718 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq663 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq663
    | exact resolve eq663 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq905 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq119
  have eq963 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq905 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq1389 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq256 X0
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq256
    | exact resolve eq256 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1399 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1389 eq14
    | exact resolve eq14 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq1584 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq675 X0
       have i₂ := eq252 x
       grind)
    | exact superpose eq252 eq675
    | exact resolve eq675 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq1589 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1584 eq14
    | exact resolve eq14 eq1584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq1670 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq676 X0
       have i₂ := eq252 sF2
       grind)
    | exact superpose eq252 eq676
    | exact resolve eq676 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq676
  have eq1680 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1670 eq1399
    | exact resolve eq1399 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399 eq1670
  have eq12438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq12439 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12438
    | exact resolve eq12438 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12438
  have eq12450 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12439
       have r₂ := eq27
       grind)
    | exact resolve eq12439 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12439
  have eq12454 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12450
    | exact resolve eq12450 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12450
  have eq12456 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12454
    | exact resolve eq12454 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12454
  have eq12524 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12456 eq718
    | exact resolve eq718 eq12456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12456
  have eq12533 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1680 eq12524
    | exact resolve eq12524 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12524
  have eq12612 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq718 y y x
       have i₂ := eq12533
       grind)
    | exact superpose eq12533 eq718
    | exact resolve eq718 eq12533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12533
  have eq12621 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1589 eq12612
    | exact resolve eq12612 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12612
  have eq12647 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12621 eq65
    | (have r₁ := eq65
       have r₂ := eq12621
       grind)
    | exact resolve eq65 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq12621
  have eq12663 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq12647
  have eq12924 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12663 eq91
    | exact resolve eq91 eq12663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq12663
  have eq12945 : (M.op y y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq12924
    | exact resolve eq12924 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq12924
  have eq12948 : (M.op y y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12945
       have r₂ := eq64
       grind)
    | exact resolve eq12945 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12945
  have eq12959 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq12948
       grind)
    | exact superpose eq12948 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12948
  have eq12960 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12959
  have eq12962 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12960
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12960
    | exact resolve eq12960 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12960
  have eq12972 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12962
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12962
    | exact resolve eq12962 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12962
  have eq13076 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq718 y y x
       have i₂ := eq12972
       grind)
    | exact superpose eq12972 eq718
    | exact resolve eq718 eq12972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12972
  have eq13085 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1589 eq13076
    | exact resolve eq13076 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589 eq13076
  have eq13086 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq13085
  have eq13112 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13086 eq29
    | exact resolve eq29 eq13086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13086
  have eq13228 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq13112
    | exact resolve eq13112 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13112
  have eq13229 : y = (M.op x y) ∨ x = y := by grind
  clear eq13228
  have eq13244 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13229 eq20
    | exact resolve eq20 eq13229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13248 : y ≠ y ∨ (M.op y y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq13229 eq64
    | (have r₁ := eq64
       have r₂ := eq13229
       grind)
    | exact resolve eq64 eq13229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq13229
  have eq13321 : (M.op y y) = (k y x) ∨ x = y := by grind
  clear eq13248
  have eq13375 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13244
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13244
    | exact resolve eq13244 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13244
  have eq15194 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq963 x y
       have i₂ := eq13321
       grind)
    | exact superpose eq13321 eq963
    | (have j0 := eq963 x y
       grind)
    | exact resolve eq963 eq13321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq13321
  have eq15280 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq15194
  have eq15341 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq15280
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq15280
    | exact resolve eq15280 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq15280
  have eq15410 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq15341
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15341
    | exact resolve eq15341 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15341
  have eq15478 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq15410
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15410
    | exact resolve eq15410 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15410
  have eq15535 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq15478
    | exact resolve eq15478 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15478
  have eq15589 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq15535
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15535
    | exact resolve eq15535 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15535
  have eq15637 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq15589
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15589
    | exact resolve eq15589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15589
  have eq15647 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq15637
    | exact resolve eq15637 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15637
  have eq16751 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15647 eq718
    | exact resolve eq718 eq15647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq15647
  have eq16766 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1680 eq16751
    | exact resolve eq16751 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680 eq16751
  have eq17201 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16766 eq27
    | exact resolve eq27 eq16766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16766
  have eq17224 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17201
       have r₂ := eq13375
       grind)
    | exact resolve eq17201 eq13375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13375 eq17201
  have eq17227 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17224 eq29
    | exact resolve eq29 eq17224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17224
  have eq17374 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq17227
    | exact resolve eq17227 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17227
  have eq17375 : x = y := by grind
  clear eq17374
  have eq17391 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17375
       grind)
    | exact superpose eq17375 eq18
    | exact resolve eq18 eq17375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq17392 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17375
       grind)
    | exact superpose eq17375 eq24
    | exact resolve eq24 eq17375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17375
  have eq17509 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17392
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17392
    | exact resolve eq17392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17392
  have eq17529 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17509 eq26
    | exact resolve eq26 eq17509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17509
  have eq18354 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17529 eq116
    | exact resolve eq116 eq17529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq17529
  have eq18469 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18354
       have i₂ := eq17391
       grind)
    | exact superpose eq17391 eq18354
    | exact resolve eq18354 eq17391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17391 eq18354
  have eq18480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18469 eq15
    | exact resolve eq15 eq18469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18469
  have eq18524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18480
    | exact resolve eq18480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq18480
  have eq18533 : False := by grind
  exact eq18533
