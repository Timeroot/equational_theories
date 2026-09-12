import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq29 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq31 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq31 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq36
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq40 X0 X1
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq40 X0 X1
       grind)
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq43 X0 X1
       grind)
    | (have r₁ := eq95 X0 X1
       have r₂ := eq43 X0 X1
       grind)
    | (have r₁ := eq95 X0 X0
       have r₂ := eq43 X0 X0
       grind)
    | exact resolve eq95 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq95
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq202
    | exact resolve eq202 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq202
  have eq211 : False := by grind
  exact eq211

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq63 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq72 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq23
  have eq325 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq325
  have eq333 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq329 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq346 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq333 (σ X0)
       grind)
    | exact superpose eq333 eq15
    | exact resolve eq15 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq333 (τ X0)
       grind)
    | exact superpose eq333 eq32
    | exact resolve eq32 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq352 X0
       have i₂ := eq333 X0
       grind)
    | exact superpose eq333 eq352
    | exact resolve eq352 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq365 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq346 X0
       have i₂ := eq333 X0
       grind)
    | exact superpose eq333 eq346
    | exact resolve eq346 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq346
  have eq415 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq416 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq365 X0
       grind)
    | exact superpose eq365 eq63
    | exact resolve eq63 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq415 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq415
    | exact resolve eq415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq426 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq419
  have eq617 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 X1 X2
       have i₂ := eq14 (k (σ X0) X1) (σ X2)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (k (σ X0) X1) (σ X2)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq623 X0 X1 X2
       have i₂ := eq365 X2
       grind)
    | exact superpose eq365 eq623
    | (have j0 := eq623 X0 X1 X2
       grind)
    | exact resolve eq623 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq7270 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq617 X0 (σ (M.op X0 X0))
       have i₂ := eq416 X0
       grind)
    | exact superpose eq416 eq617
    | (have j0 := eq617 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq617 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq617
  have eq7391 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7270 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7270
    | (have j0 := eq7270 X0
       grind)
    | exact resolve eq7270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7270
  have eq7412 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7391 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7391
    | (have j0 := eq7391 X0
       grind)
    | exact resolve eq7391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7391
  have eq7430 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) X0)) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7412 X0
       have i₂ := eq426 X0
       grind)
    | exact superpose eq426 eq7412
    | (have j0 := eq7412 X0
       grind)
    | exact resolve eq7412 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7412
  have eq7446 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ X0) = (σ (M.op (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7430 X0
       have i₂ := eq365 (M.op X0 X0)
       grind)
    | exact superpose eq365 eq7430
    | (have j0 := eq7430 X0
       grind)
    | exact resolve eq7430 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7430
  have eq19128 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq7446 (τ X0)
       grind)
    | exact superpose eq7446 eq18
    | (have j1 := eq7446 (τ X0)
       grind)
    | exact resolve eq18 eq7446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7446
  have eq19181 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19128 X0
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq19128
    | (have j0 := eq19128 X0
       grind)
    | exact resolve eq19128 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19128
  have eq19244 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19181 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19181
    | (have j0 := eq19181 X0
       grind)
    | exact resolve eq19181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19181
  have eq19302 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19244 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19244
    | (have j0 := eq19244 X0
       grind)
    | exact resolve eq19244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19244
  have eq19354 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19302 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq19302
    | (have j0 := eq19302 X0
       grind)
    | exact resolve eq19302 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq19302
  have eq19405 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ (M.op X0 X0))) X0) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19354 X0
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq19354
    | (have j0 := eq19354 X0
       grind)
    | exact resolve eq19354 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19354
  have eq19456 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19405 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19405
    | (have j0 := eq19405 X0
       grind)
    | exact resolve eq19405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19405
  have eq19507 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq19456
  have eq19555 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19507 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19507
    | (have j0 := eq19507 X0
       grind)
    | exact resolve eq19507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19507
  have eq19592 : ∀ X0 : G, (σ (τ X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19555 X0
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq19555
    | (have j0 := eq19555 X0
       grind)
    | exact resolve eq19555 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19555
  have eq19613 : ∀ X0 : G, (σ (τ X0)) = (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19592 X0
       have i₂ := eq359 (M.op X0 X0)
       grind)
    | exact superpose eq359 eq19592
    | (have j0 := eq19592 X0
       grind)
    | exact resolve eq19592 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19592
  have eq19634 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19613 X0
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq19613
    | (have j0 := eq19613 X0
       grind)
    | exact resolve eq19613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19613
  have eq19653 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19634 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19634
    | (have j0 := eq19634 X0
       grind)
    | exact resolve eq19634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19634
  have eq19703 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq19653 X0
       grind)
    | exact superpose eq19653 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       have j1 := eq19653 X0
       grind)
    | exact resolve eq13 eq19653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19653
  have eq19709 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq19703 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19703
  have eq19713 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq19709 X0
       grind)
    | (have r₁ := eq19709 X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq19709 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19709
  have eq19745 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq19713
  have eq19842 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19745 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq19745
    | (have j0 := eq19745 X0
       grind)
    | exact resolve eq19745 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq19745
  have eq19843 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq19842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19842
  have eq396150 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq626 X0 X1 X2
       grind)
    | exact superpose eq626 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq626 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq626 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq626 X0 X1 X2
       grind)
    | exact resolve eq13 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq396152 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq396150 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396150
  have eq396156 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X2 X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396152 X0 X1 X2
       have i₂ := eq365 X2
       grind)
    | exact superpose eq365 eq396152
    | (have j0 := eq396152 X0 X1 X2
       grind)
    | exact resolve eq396152 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq396152
  have eq396157 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X2 X2)) ∨ (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq396156 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396156
  have eq396509 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396157 X0 X1 X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq396157
    | (have j0 := eq396157 X0 X1 X2
       grind)
    | exact resolve eq396157 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq396157
  have eq396510 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq396509 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396509
  have eq396922 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (k (σ (τ X0)) X1) (σ X2)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396510 (τ X0) X1 X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq396510
    | (have j0 := eq396510 (τ X0) X1 X2
       grind)
    | exact resolve eq396510 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq396510
  have eq397770 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396922 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq396922
    | (have j0 := eq396922 X0 X1 X2
       grind)
    | exact resolve eq396922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396922
  have eq398079 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq397770 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq397770
    | (have j0 := eq397770 X0 X1 X2
       grind)
    | exact resolve eq397770 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq397770
  have eq398304 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (k X0 X1) (σ X2)) ∨ (k X0 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq398079 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq398079
    | (have j0 := eq398079 X0 X1 X2
       grind)
    | exact resolve eq398079 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398079
  have eq398844 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq398304 X0 (M.op X0 X0) x
       have i₂ := eq19843 X0
       grind)
    | exact superpose eq19843 eq398304
    | exact resolve eq398304 eq19843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19843 eq398304
  have eq399742 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq398844 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq398844
    | (have j0 := eq398844 X1 (τ X0)
       grind)
    | exact resolve eq398844 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398844
  have eq400604 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq399742 X0 X1
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq399742
    | (have j0 := eq399742 X0 X1
       grind)
    | exact resolve eq399742 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq399742
  have eq400638 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq400604 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq400604
    | (have j0 := eq400604 X0 X1
       grind)
    | exact resolve eq400604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400604
  have eq401296 : ∀ X0 X1 : G, (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq400638 X1 (σ X0)
       grind)
    | exact superpose eq400638 eq29
    | (have j1 := eq400638 X1 (σ X0)
       grind)
    | exact resolve eq29 eq400638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq407019 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0
       have i₂ := eq401296 X0 (σ X0)
       grind)
    | exact superpose eq401296 eq72
    | (have j1 := eq401296 X0 (σ X1)
       grind)
    | exact resolve eq72 eq401296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq401296
  have eq407066 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq407019 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq407019
    | (have j0 := eq407019 X0 X1
       grind)
    | exact resolve eq407019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407019
  have eq407274 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq407066 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq407066
    | (have j0 := eq407066 X0 X1
       grind)
    | exact resolve eq407066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407066
  have eq407275 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq407274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407274
  have eq407864 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq407275 X0 X1
       grind)
    | exact superpose eq407275 eq11
    | exact resolve eq11 eq407275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407275
  have eq414305 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq407864 x y
       grind)
    | exact superpose eq407864 eq16
    | exact resolve eq16 eq407864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407864
  have eq415153 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq414305
       have i₂ := eq400638 y x
       grind)
    | exact superpose eq400638 eq414305
    | (have j1 := eq400638 y x
       grind)
    | exact resolve eq414305 eq400638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400638 eq414305
  have eq415159 : x = (M.op y y) := by grind
  clear eq415153
  have eq415167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq426 y
       have i₂ := eq415159
       grind)
    | exact superpose eq415159 eq426
    | exact resolve eq426 eq415159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq415159
  have eq415275 : False := by grind
  exact eq415275

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 (M.op x x)) X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X0 X1) X0)) = X0 ∨ (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X1) X0)
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 X0 (M.op (M.op X0 X1) X0)
       grind)
    | (have r₁ := eq13 X1 (M.op (M.op X1 X0) X1)
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)) = X0 ∨ (k X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq32
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq39
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq39 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq104 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq72
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq460 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (k X0 (M.op (M.op X0 X1) X0)) ∨ (k X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    grind
  clear eq46
  have eq466 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) X0)) = X0 ∨ (k X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq460 X0 X1
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq460
    | (have j0 := eq460 X0 X1
       grind)
    | exact resolve eq460 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq460
  have eq467 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq466 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq483 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op (τ X0) X1) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (M.op (τ X0) X1) (τ X0))
       have i₂ := eq467 (τ X0) X1
       grind)
    | exact superpose eq467 eq18
    | exact resolve eq18 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq486 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op (τ X0) X1) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq483 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq483
    | exact resolve eq483 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq510 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op (τ (τ X0)) X1) (τ (τ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (M.op (M.op (τ (τ X0)) X1) (τ (τ X0))))
       have i₂ := eq486 (τ X0) X1
       grind)
    | exact superpose eq486 eq18
    | exact resolve eq18 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq517 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op (τ (τ X0)) X1) (τ (τ X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq510
    | exact resolve eq510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq1449 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq104 X0 X1 X2
       grind)
    | exact superpose eq104 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq104 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq104 X0 X1 X2
       grind)
    | exact resolve eq13 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1452 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1449 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1453 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1452 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1454 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1453 X0 X1 X2
       have i₂ := eq31 X0 X1 X2
       grind)
    | exact superpose eq31 eq1453
    | (have j0 := eq1453 X0 X1 X2
       grind)
    | exact resolve eq1453 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1453
  have eq2046 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0))))))
       have i₂ := eq517 (τ X0) X1
       grind)
    | exact superpose eq517 eq18
    | exact resolve eq18 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq2059 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (M.op (τ (τ (τ X0))) X1) (τ (τ (τ X0)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2046 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2046
    | exact resolve eq2046 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq9725 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq9726 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq9725 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9725
  have eq9733 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9726 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9726
    | (have j0 := eq9726 X0
       grind)
    | exact resolve eq9726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9726
  have eq12592 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq9733 X0
       grind)
    | exact superpose eq9733 eq52
    | (have j1 := eq9733 X0
       grind)
    | exact resolve eq52 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq9733
  have eq12624 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12592 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12592
    | (have j0 := eq12592 X0
       grind)
    | exact resolve eq12592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12592
  have eq12625 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12624 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12624
  have eq12711 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12625 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12625
    | exact resolve eq12625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12753 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq12625 X0
       grind)
    | exact superpose eq12625 eq11
    | exact resolve eq11 eq12625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12625
  have eq12825 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12711 X0
       have i₂ := eq48 X0 X0
       grind)
    | exact superpose eq48 eq12711
    | exact resolve eq12711 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12711
  have eq13256 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq12825 X0
       grind)
    | exact superpose eq12825 eq11
    | exact resolve eq11 eq12825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13339 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13256 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq13256
    | exact resolve eq13256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13256
  have eq13446 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0 X0
       have i₂ := eq13339 (τ X0)
       grind)
    | exact superpose eq13339 eq48
    | exact resolve eq48 eq13339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq13492 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13446 X0
       have i₂ := eq12825 X0
       grind)
    | exact superpose eq12825 eq13446
    | exact resolve eq13446 eq12825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12825 eq13446
  have eq14034 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq14082 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14034 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq14034
    | exact resolve eq14034 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14034
  have eq14144 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14082 X0
       have i₂ := eq13339 X0
       grind)
    | exact superpose eq13339 eq14082
    | exact resolve eq14082 eq13339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14082
  have eq14183 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq14144
  have eq39989 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ X0)))) X1) (τ (τ (τ (τ X0)))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (M.op (M.op (τ (τ (τ (τ X0)))) X1) (τ (τ (τ (τ X0))))))))
       have i₂ := eq2059 (τ X0) X1
       grind)
    | exact superpose eq2059 eq18
    | exact resolve eq18 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq40043 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ X0)))) X1) (τ (τ (τ (τ X0)))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39989 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39989
    | exact resolve eq39989 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39989
  have eq65665 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1454 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq65666 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65665 X0 X1 X2
       have j1 := eq104 X0 X1 X2
       grind)
    | (have r₁ := eq65665 X0 X1 X2
       have r₂ := eq104 X0 X1 X2
       grind)
    | exact resolve eq65665 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq65665
  have eq65922 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k X2 X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65666 X0 X1 X2
       have i₂ := eq12753 X2
       grind)
    | exact superpose eq12753 eq65666
    | (have j0 := eq65666 X0 X1 X2
       grind)
    | exact resolve eq65666 eq12753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12753 eq65666
  have eq66171 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65922 X0 X1 X2
       have i₂ := eq13339 X2
       grind)
    | exact superpose eq13339 eq65922
    | (have j0 := eq65922 X0 X1 X2
       grind)
    | exact resolve eq65922 eq13339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13339 eq65922
  have eq176210 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0)))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0))))))))))
       have i₂ := eq40043 (τ X0) X1
       grind)
    | exact superpose eq40043 eq18
    | exact resolve eq18 eq40043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176299 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0)))))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176210 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176210
    | exact resolve eq176210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176210
  have eq225552 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0)))))))))))) (σ X2)) ∨ (σ (M.op X2 X2)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66171 X0 (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0)))))))))) X2
       have i₂ := eq40043 (τ X0) X1
       grind)
    | exact superpose eq40043 eq66171
    | (have j0 := eq66171 X0 (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0)))))))))) X2
       grind)
    | exact resolve eq66171 eq40043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40043 eq66171
  have eq226391 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (σ (M.op X2 X2)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq225552 X0 X1 X2
       have i₂ := eq176299 X0 X1
       grind)
    | exact superpose eq176299 eq225552
    | (have j0 := eq225552 X0 X1 X2
       grind)
    | exact resolve eq225552 eq176299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225552
  have eq226781 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ (M.op X2 X2)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op (τ (τ (τ (τ (τ X0))))) X1) (τ (τ (τ (τ (τ X0)))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq226391 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq226391
    | (have j0 := eq226391 X0 X1 X2
       grind)
    | exact resolve eq226391 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226391
  have eq227072 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ (M.op X2 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq226781 X0 x X2
       have i₂ := eq176299 X0 x
       grind)
    | exact superpose eq176299 eq226781
    | (have j0 := eq226781 X0 x X2
       grind)
    | exact resolve eq226781 eq176299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176299 eq226781
  have eq228011 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq227072 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227072
    | (have j0 := eq227072 X1 (τ X0)
       grind)
    | exact resolve eq227072 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228329 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq227072 (σ X0) X1
       grind)
    | exact superpose eq227072 eq15
    | (have j1 := eq227072 (σ X0) X1
       grind)
    | exact resolve eq15 eq227072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227072
  have eq228753 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq228011 X0 X1
       have i₂ := eq13492 X0
       grind)
    | exact superpose eq13492 eq228011
    | (have j0 := eq228011 X0 X1
       grind)
    | exact resolve eq228011 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13492 eq228011
  have eq229005 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq228753 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq228753
    | (have j0 := eq228753 X0 X1
       grind)
    | exact resolve eq228753 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228753
  have eq230103 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq229005 X1 (τ X0)
       grind)
    | exact superpose eq229005 eq18
    | (have j1 := eq229005 X1 (τ X0)
       grind)
    | exact resolve eq18 eq229005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq229005
  have eq238121 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq230103 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq230103
    | exact resolve eq230103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230103
  have eq238837 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq238121 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq238121
    | (have j0 := eq238121 X0 X1
       grind)
    | exact resolve eq238121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238121
  have eq248981 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq228329 x y
       grind)
    | exact superpose eq228329 eq16
    | (have j1 := eq228329 x y
       grind)
    | exact resolve eq16 eq228329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228329
  have eq249920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq248981
       have i₂ := eq238837 x y
       grind)
    | exact superpose eq238837 eq248981
    | (have j1 := eq238837 x y
       grind)
    | (have r₁ := eq248981
       have r₂ := eq238837 x y
       grind)
    | exact resolve eq248981 eq238837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238837 eq248981
  have eq249923 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq249920
  have eq251904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq14183 y
       have i₂ := eq249923
       grind)
    | exact superpose eq249923 eq14183
    | exact resolve eq14183 eq249923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249923
  have eq251962 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq251904
       have r₂ := eq16
       grind)
    | exact resolve eq251904 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251904
  have eq252027 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq251962
       grind)
    | exact superpose eq251962 eq10
    | exact resolve eq10 eq251962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251962
  have eq252424 : x = (M.op y y) := by
    first
    | (have i₁ := eq252027
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq252027
    | exact resolve eq252027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252027
  have eq254565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14183 y
       have i₂ := eq252424
       grind)
    | exact superpose eq252424 eq14183
    | exact resolve eq14183 eq252424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14183 eq252424
  have eq254637 : False := by grind
  exact eq254637

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq278 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq281 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq279 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq279 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq279 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq292 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq281 (σ X0)
       grind)
    | exact superpose eq281 eq15
    | exact resolve eq15 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq281 X0
       grind)
    | exact superpose eq281 eq292
    | exact resolve eq292 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq292
  have eq357 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq311 X0
       grind)
    | exact superpose eq311 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq311 X0
       grind)
    | exact superpose eq311 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
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
  clear eq357
  have eq509 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq360 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq360
    | exact resolve eq360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq360 X1 (σ X0)
       grind)
    | exact superpose eq360 eq15
    | (have j1 := eq360 X1 (σ X0)
       grind)
    | exact resolve eq15 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq590 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq509 X1 (τ X0)
       grind)
    | exact superpose eq509 eq17
    | (have j1 := eq509 X1 (τ X0)
       grind)
    | exact resolve eq17 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq509
  have eq939 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq590
    | exact resolve eq590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq1004 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq939 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq939
    | (have j0 := eq939 X0 X1
       grind)
    | exact resolve eq939 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq2022 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq520 x y
       grind)
    | exact superpose eq520 eq16
    | (have j1 := eq520 x y
       grind)
    | exact resolve eq16 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2061 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq2204 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2061 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2061
    | (have j0 := eq2061 (τ X0) (τ X1)
       grind)
    | exact resolve eq2061 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2209 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2061 X0 X1
       have i₂ := eq1004 X0 X1
       grind)
    | exact superpose eq1004 eq2061
    | (have j0 := eq2061 X0 X1
       have j1 := eq1004 (σ X0) (σ X1)
       grind)
    | exact resolve eq2061 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2214 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2204 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2204
    | (have j0 := eq2204 X0 X1
       grind)
    | exact resolve eq2204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2221 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2214 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2214
    | (have j0 := eq2214 X0 X1
       grind)
    | exact resolve eq2214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2222 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2221 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2221
    | (have j0 := eq2221 X0 X1
       grind)
    | exact resolve eq2221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2223 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2222 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2222
    | (have j0 := eq2222 X0 X1
       grind)
    | exact resolve eq2222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2369 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2022
       have i₂ := eq1004 x y
       grind)
    | exact superpose eq1004 eq2022
    | (have j1 := eq1004 (σ x) (σ y)
       grind)
    | (have r₁ := eq2022
       have r₂ := eq1004 x y
       grind)
    | exact resolve eq2022 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004 eq2022
  have eq2370 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2369
  have eq2373 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2370
       grind)
    | exact superpose eq2370 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2370
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2370
       grind)
    | exact resolve eq13 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2376 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq2373
  have eq4019 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2376
       grind)
    | exact superpose eq2376 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2376
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq2376
       grind)
    | exact resolve eq13 eq2376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376
  have eq4022 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq4019
  have eq4023 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4022
       have i₂ := eq311 y
       grind)
    | exact superpose eq311 eq4022
    | exact resolve eq4022 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022
  have eq4025 : y = (k x y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4023
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4023
    | exact resolve eq4023 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4023
  have eq1394446 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2061 x y
       have i₂ := eq4025
       grind)
    | exact superpose eq4025 eq2061
    | (have j0 := eq2061 x y
       grind)
    | (have r₁ := eq2061 x y
       have r₂ := eq4025
       grind)
    | exact resolve eq2061 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4025
  have eq1394549 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op y y) := by grind
  clear eq1394446
  have eq1394553 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq2061 x y
       grind)
    | (have r₁ := eq1394549
       have r₂ := eq2061 x y
       grind)
    | exact resolve eq1394549 eq2061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061 eq1394549
  have eq1394557 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1394553
       grind)
    | exact superpose eq1394553 eq16
    | exact resolve eq16 eq1394553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1394609 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1394553
       grind)
    | exact superpose eq1394553 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1394553
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1394553
       grind)
    | exact resolve eq13 eq1394553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394553
  have eq1394757 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1394609
  have eq1394869 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq2209 y y
       grind)
    | (have r₁ := eq1394757
       have r₂ := eq2209 y y
       grind)
    | exact resolve eq1394757 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209 eq1394757
  have eq1394940 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1394869
       have i₂ := eq311 y
       grind)
    | exact superpose eq311 eq1394869
    | exact resolve eq1394869 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq1394869
  have eq1394991 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1394940
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1394940
    | exact resolve eq1394940 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394940
  have eq1395053 : (k x y) = (τ (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1394991
       grind)
    | exact superpose eq1394991 eq10
    | exact resolve eq10 eq1394991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394991
  have eq1395527 : y = (k x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1395053
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1395053
    | exact resolve eq1395053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395053
  have eq1395563 : y ≠ y ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2223 x y
       have i₂ := eq1395527
       grind)
    | exact superpose eq1395527 eq2223
    | (have j0 := eq2223 x y
       grind)
    | (have r₁ := eq2223 x y
       have r₂ := eq1395527
       grind)
    | exact resolve eq2223 eq1395527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223 eq1395527
  have eq1395662 : y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1395563
  have eq1395678 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1394557
       have i₂ := eq1395662
       grind)
    | exact superpose eq1395662 eq1394557
    | exact resolve eq1394557 eq1395662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394557 eq1395662
  have eq1395837 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1395678
  have eq1395838 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1395837
  have eq1395924 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1395838
       grind)
    | exact superpose eq1395838 eq10
    | exact resolve eq10 eq1395838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395838
  have eq1396411 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1395924
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1395924
    | exact resolve eq1395924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395924
  have eq1396412 : y = (M.op y y) := by grind
  clear eq1396411
  have eq1396470 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq1396412
       grind)
    | exact superpose eq1396412 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq1396412
       grind)
    | exact resolve eq12 eq1396412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396474 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq358 y X0
       have i₂ := eq1396412
       grind)
    | exact superpose eq1396412 eq358
    | (have j0 := eq358 y X0
       grind)
    | exact resolve eq358 eq1396412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq1396412
  have eq1396889 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1396474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396474
  have eq1396891 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq1396470 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396470
  have eq1399858 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1396889 (σ X0)
       grind)
    | exact superpose eq1396889 eq15
    | exact resolve eq15 eq1396889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396889
  have eq1400240 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1399858 X0
       have i₂ := eq1396891 X0
       grind)
    | exact superpose eq1396891 eq1399858
    | exact resolve eq1399858 eq1396891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396891 eq1399858
  have eq1410142 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1400240 x
       grind)
    | exact superpose eq1400240 eq16
    | (have r₁ := eq16
       have r₂ := eq1400240 x
       grind)
    | exact resolve eq16 eq1400240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400240
  have eq1411459 : False := by grind
  exact eq1411459

/-- `Equation1052`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation1052 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1052 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1052.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X1)) = X0 := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq55 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 (M.op y y) y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq37
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq55
    | exact resolve eq55 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq991 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq420 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq55 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq55 eq420
    | exact resolve eq420 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq1076 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq991 X0 X1
       have i₂ := eq45 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq45 eq991
    | exact resolve eq991 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq991
  have eq1092 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq55 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq55 eq1076
    | exact resolve eq1076 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq30734 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq30735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq30734
    | exact resolve eq30734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30734
  have eq30746 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq30735
       have r₂ := eq28
       grind)
    | exact resolve eq30735 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30735
  have eq31190 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30746 eq127
    | exact resolve eq127 eq30746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq30746
  have eq31273 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq31190
    | exact resolve eq31190 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31190
  have eq31274 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31273
  have eq31280 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq31274
       grind)
    | exact superpose eq31274 eq96
    | exact resolve eq96 eq31274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31288 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq55 y X0
       have i₂ := eq31274
       grind)
    | exact superpose eq31274 eq55
    | exact resolve eq55 eq31274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq31307 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1092 y X0
       have i₂ := eq31274
       grind)
    | exact superpose eq31274 eq1092
    | exact resolve eq1092 eq31274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq31352 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq31307 X0
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq31307
    | exact resolve eq31307 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq31307
  have eq31364 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31280
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31280
    | exact resolve eq31280 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31280
  have eq31460 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq31288 X0
       have i₂ := eq31274
       grind)
    | exact superpose eq31274 eq31288
    | exact resolve eq31288 eq31274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31274 eq31288
  have eq31619 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq31460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31460
  have eq31649 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq31619 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31619
    | (have j0 := eq31619 x
       grind)
    | exact resolve eq31619 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31619
  have eq31829 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31649 eq30
    | exact resolve eq30 eq31649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31649
  have eq31929 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq31829
    | exact resolve eq31829 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31829
  have eq31930 : x = (M.op x y) ∨ x = y := by grind
  clear eq31929
  have eq32572 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31930 eq21
    | exact resolve eq21 eq31930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31930
  have eq32689 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq32572
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32572
    | exact resolve eq32572 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32572
  have eq32704 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq32689 eq27
    | exact resolve eq27 eq32689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32689
  have eq49076 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31364 eq31352
    | exact resolve eq31352 eq31364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31352 eq31364
  have eq49263 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq49076 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49076
  have eq49444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq49263 eq32704
    | exact resolve eq32704 eq49263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32704 eq49263
  have eq49457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq49444
  have eq49470 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq49457
       have r₂ := eq28
       grind)
    | exact resolve eq49457 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49457
  have eq49516 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq49470 eq30
    | exact resolve eq30 eq49470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq49470
  have eq49642 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq49516
    | exact resolve eq49516 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq49516
  have eq49643 : x = y := by grind
  clear eq49642
  have eq49662 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq49643
       grind)
    | exact superpose eq49643 eq19
    | exact resolve eq19 eq49643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq49663 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq49643
       grind)
    | exact superpose eq49643 eq25
    | exact resolve eq25 eq49643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq49643
  have eq49784 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq49663
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq49663
    | exact resolve eq49663 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq49663
  have eq49803 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq49784 eq27
    | exact resolve eq27 eq49784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq49784
  have eq50078 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq49803 eq69
    | exact resolve eq69 eq49803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq49803
  have eq50162 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq50078
       have i₂ := eq49662
       grind)
    | exact superpose eq49662 eq50078
    | exact resolve eq50078 eq49662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49662 eq50078
  have eq50171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50162 eq15
    | exact resolve eq15 eq50162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50162
  have eq50250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq50171
    | exact resolve eq50171 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq50171
  have eq50271 : False := by grind
  exact eq50271

/-- `Equation1060`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation1060 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1060 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1060.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13 (σ x) (σ y)
       grind)
    | exact superpose eq13 eq16
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17
    | exact resolve eq17 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq22 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq19
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq19
       have r₂ := eq13 x (σ x)
       grind)
    | (have r₁ := eq19
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq19 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq23 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq22
  have eq24 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq24
  have eq27 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq23
       have i₂ := eq14 (σ y) (σ y)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq23
       have r₂ := eq14 (σ x) x
       grind)
    | (have r₁ := eq23
       have r₂ := eq14 x (σ x)
       grind)
    | (have r₁ := eq23
       have r₂ := eq14 x x
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq27
  have eq31 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq30
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq30
       have r₂ := eq12 x (σ y)
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq32 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq31
    | exact resolve eq31 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32
       have i₂ := eq14 (σ x) (σ x)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq32
       have r₂ := eq14 (σ x) x
       grind)
    | (have r₁ := eq32
       have r₂ := eq14 x (σ x)
       grind)
    | (have r₁ := eq32
       have r₂ := eq14 x x
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq33
  have eq36 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq35
       have r₂ := eq32
       grind)
    | exact resolve eq35 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq35
  have eq37 : (σ y) = (σ (k y y)) ∨ (σ x) ≠ (σ (k x x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq36
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : (k y y) = (τ (σ y)) ∨ (σ x) ≠ (σ (k x x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq37
       grind)
    | exact superpose eq37 eq10
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq41 : y = (k y y) ∨ (σ x) ≠ (σ (k x x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq40
    | exact resolve eq40 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq44 : (σ x) ≠ (σ (k x x)) ∨ y = (k y y) ∨ x ≠ (M.op x x) := by
    first
    | (have j1 := eq12 y y
       grind)
    | (have r₁ := eq41
       have r₂ := eq12 x y
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq45 : (σ x) ≠ (σ x) ∨ y = (k y y) ∨ x ≠ (M.op x x) ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq44
    | (have j1 := eq12 y y
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : (σ x) ≠ (σ x) ∨ y = (k y y) ∨ x ≠ (M.op x x) := by grind
  clear eq45
  have eq47 : y = (k y y) ∨ x ≠ (M.op x x) := by grind
  clear eq46
  have eq48 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq14 (σ y) (σ y)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq48
  have eq52 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq51
       have r₂ := eq12 x (σ x)
       grind)
    | (have r₁ := eq51
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq51
       have r₂ := eq12 x x
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq52
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq52
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq53
       have i₂ := eq14 (σ x) (σ x)
       grind)
    | exact superpose eq14 eq53
    | (have j1 := eq14 y y
       grind)
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq60 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq55
  have eq61 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq60
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq60
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq60
       have r₂ := eq12 x (σ x)
       grind)
    | exact resolve eq60 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq62 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq61
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq61
    | exact resolve eq61 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq65 : (k y y) = (τ (σ y)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq62
       grind)
    | exact superpose eq62 eq10
    | exact resolve eq10 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq66 : y = (k y y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq65
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : y = (k y y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq12 y y
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 x x
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq69
       have r₂ := eq47
       grind)
    | exact resolve eq69 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ x) (σ X0)) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq15 (k x x) X0
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq15
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k x x) = (τ (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq77 : y = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq74
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq78 : ∀ X0 : G, (σ (k (k x x) X0)) = (σ (k x X0)) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq15 x X0
       grind)
    | exact superpose eq15 eq73
    | exact resolve eq73 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq83 : ∀ X0 : G, (k (k x x) X0) = (τ (σ (k x X0))) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k x x) X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq10
    | exact resolve eq10 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : ∀ X0 : G, (k (k x x) X0) = (k x X0) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq10 (k x X0)
       grind)
    | exact superpose eq10 eq83
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq87 : ∀ X0 : G, (k x x) = (k x X0) ∨ y = (k y y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq12 (k x x) X0
       grind)
    | exact superpose eq12 eq84
    | (have j1 := eq12 y y
       grind)
    | exact resolve eq84 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq785 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (M.op (σ y) (σ y))
       have i₂ := eq29 (σ y)
       grind)
    | exact superpose eq29 eq9
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1015 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (M.op (σ y) (σ y))
       have i₂ := eq50 (σ y)
       grind)
    | exact superpose eq50 eq9
    | exact resolve eq9 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1161 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq785 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq785
    | exact resolve eq785 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq785
  have eq1172 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1161 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq1982 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1015 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1015
    | exact resolve eq1015 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1015
  have eq1995 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1982 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq4830 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1172 X0
       have i₂ := eq14 (σ x) (σ x)
       grind)
    | exact superpose eq14 eq1172
    | (have j0 := eq1172 X0
       have j1 := eq14 y y
       grind)
    | (have r₁ := eq1172 X0
       have r₂ := eq14 (σ x) x
       grind)
    | (have r₁ := eq1172 X0
       have r₂ := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq1172 X0
       have r₂ := eq14 x x
       grind)
    | exact resolve eq1172 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4832 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830
  have eq4834 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq4832 X0
       have j1 := eq1172 X0
       grind)
    | (have r₁ := eq4832 X0
       have r₂ := eq1172 X0
       grind)
    | exact resolve eq4832 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq4832
  have eq4835 : ∀ X0 : G, (σ x) ≠ (σ (k x x)) ∨ (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq4834 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4834
    | (have j0 := eq4834 X0
       grind)
    | exact resolve eq4834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4834
  have eq5030 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1995 X0
       have i₂ := eq14 (σ x) (σ x)
       grind)
    | exact superpose eq14 eq1995
    | (have j0 := eq1995 X0
       have j1 := eq14 y y
       grind)
    | exact resolve eq1995 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995
  have eq5039 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq5030 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5030
  have eq5040 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq5039 X0
       have j1 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq5039 (σ y)
       have r₂ := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq5039 X0
       have r₂ := eq12 X0 y
       grind)
    | (have r₁ := eq5039 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq5039 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039
  have eq5041 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5040 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq5040
    | (have j0 := eq5040 X0
       grind)
    | exact resolve eq5040 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5040
  have eq9235 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ x ≠ (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4835 X0
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq4835
    | (have j0 := eq4835 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq4835 (σ y)
       have r₂ := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq4835 X0
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq4835 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835
  have eq9242 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq9235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9235
  have eq9243 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq9242 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9242
  have eq9250 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ y) X0) (σ y))) = X1 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ y) X0
       have i₂ := eq9243 X0
       grind)
    | exact superpose eq9243 eq9
    | exact resolve eq9 eq9243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9328 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = X1 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq9250 X0 X1
       have i₂ := eq9243 (M.op (σ y) X0)
       grind)
    | exact superpose eq9243 eq9250
    | exact resolve eq9250 eq9243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9243 eq9250
  have eq9352 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = X1 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq9328 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9328
  have eq9396 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (σ y)
       have i₂ := eq9352 X0 X0
       grind)
    | exact superpose eq9352 eq9
    | exact resolve eq9 eq9352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9352
  have eq9525 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9396 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq9396
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq9396 X0 X1
       have r₂ := eq14 x X1
       grind)
    | (have r₁ := eq9396 X0 X1
       have r₂ := eq14 X0 x
       grind)
    | exact resolve eq9396 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9396
  have eq9562 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9525 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9525
  have eq9623 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x ≠ (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x ≠ (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9562 y X0
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq9562
    | (have j0 := eq9562 y x
       grind)
    | (have r₁ := eq9562 x x
       have r₂ := eq47
       grind)
    | exact resolve eq9562 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9562
  have eq9645 : ∀ X0 : G, y = (M.op y y) ∨ x ≠ (M.op x x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq9623 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9623
  have eq9653 : y ≠ y ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq9645 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9645
  have eq9654 : y = (M.op y y) ∨ x ≠ (M.op x x) := by grind
  clear eq9653
  have eq9659 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ x ≠ (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq9654
       grind)
    | exact superpose eq9654 eq9
    | exact resolve eq9 eq9654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9670 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x ≠ (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y (M.op y y)
       have i₂ := eq9659 y
       grind)
    | exact superpose eq9659 eq9
    | exact resolve eq9 eq9659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9659
  have eq9690 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x ≠ (M.op x x) ∨ x ≠ (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9670 X0
       have i₂ := eq9654
       grind)
    | exact superpose eq9654 eq9670
    | exact resolve eq9670 eq9654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9654 eq9670
  have eq9715 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x ≠ (M.op x x) := by
    intro X0
    first
    | (have j0 := eq9690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9690
  have eq9720 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X0) y)) = X1 ∨ x ≠ (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 y X0
       have i₂ := eq9715 X0
       grind)
    | exact superpose eq9715 eq9
    | exact resolve eq9 eq9715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9771 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = X1 ∨ x ≠ (M.op x x) ∨ x ≠ (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq9720 X0 X1
       have i₂ := eq9715 (M.op y X0)
       grind)
    | exact superpose eq9715 eq9720
    | exact resolve eq9720 eq9715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9720
  have eq9793 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = X1 ∨ x ≠ (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq9771 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771
  have eq9844 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ x ≠ (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 y
       have i₂ := eq9793 X0 X0
       grind)
    | exact superpose eq9793 eq9
    | exact resolve eq9 eq9793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9793
  have eq9886 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ x ≠ (M.op x x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9844 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq9844
    | (have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq9844 X0 X1
       have r₂ := eq14 x X1
       grind)
    | (have r₁ := eq9844 X0 X1
       have r₂ := eq14 X0 x
       grind)
    | exact resolve eq9844 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9969 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ x ≠ (M.op x x) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9886 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9886
  have eq10030 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ x ≠ (M.op x x) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9969 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq9969
    | (have j0 := eq9969 (σ X0) X1
       grind)
    | exact resolve eq9969 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9969
  have eq15585 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ x ≠ (M.op x x) ∨ x ≠ (M.op x x) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9844 (σ X0) X1
       have i₂ := eq10030 X0 X2
       grind)
    | exact superpose eq10030 eq9844
    | (have j1 := eq10030 X0 X2
       grind)
    | exact resolve eq9844 eq10030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844 eq10030
  have eq15603 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ x ≠ (M.op x x) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq15585 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15585
  have eq15668 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) ∨ (M.op X1 (σ y)) = X1 ∨ x ≠ (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq15603 y X1 X0
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq15603
    | (have j0 := eq15603 y X0 x
       grind)
    | exact resolve eq15603 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq15603
  have eq15817 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ x ≠ (M.op x x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15668 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15668
  have eq15907 : ∀ X0 : G, X0 ≠ X0 ∨ x ≠ (M.op x x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq15817 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15817
  have eq15908 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x ≠ (M.op x x) := by
    intro X0
    first
    | (have j0 := eq15907 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15907
  have eq16038 : (σ (M.op x y)) ≠ (σ x) ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15908 (σ x)
       grind)
    | exact superpose eq15908 eq16
    | exact resolve eq16 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15908
  have eq16131 : (σ x) ≠ (σ x) ∨ x ≠ (M.op x x) ∨ x ≠ (M.op x x) := by
    first
    | (have i₁ := eq16038
       have i₂ := eq9715 x
       grind)
    | exact superpose eq9715 eq16038
    | exact resolve eq16038 eq9715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9715 eq16038
  have eq16135 : (σ x) ≠ (σ x) ∨ x ≠ (M.op x x) := by grind
  clear eq16131
  have eq16136 : x ≠ (M.op x x) := by grind
  clear eq16135
  have eq16137 : x ≠ (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16136
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq16136
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq16136
       have r₂ := eq14 x x
       grind)
    | (have r₁ := eq16136
       have r₂ := eq14 x x
       grind)
    | exact resolve eq16136 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16139 : x ≠ (k x x) ∨ x = (M.op x x) := by grind
  clear eq16137
  have eq16140 : x ≠ (k x x) := by
    first
    | (have r₁ := eq16139
       have r₂ := eq16136
       grind)
    | exact resolve eq16139 eq16136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16139
  have eq16141 : ∀ X0 : G, x ≠ (k x X0) ∨ y = (k y y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq16140
       have i₂ := eq87 X0
       grind)
    | (have i₁ := eq16140
       have i₂ := eq87 x
       grind)
    | exact superpose eq87 eq16140
    | (have j1 := eq87 X0
       grind)
    | exact resolve eq16140 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq16148 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq16141 X0
       have j1 := eq12 y y
       grind)
    | (have r₁ := eq16141 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq16141 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16141
  have eq16172 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq5041 X0
       grind)
    | (have r₁ := eq5041 X0
       have r₂ := eq16136
       grind)
    | exact resolve eq5041 eq16136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5041 eq16136
  have eq16180 : ∀ X0 : G, (k x x) = (τ (σ x)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq16172 X0
       grind)
    | exact superpose eq16172 eq10
    | (have j1 := eq16172 X0
       grind)
    | exact resolve eq10 eq16172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16172
  have eq16181 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq16180 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16180
    | (have j0 := eq16180 X0
       grind)
    | exact resolve eq16180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16180
  have eq16184 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq16181 X0
       grind)
    | (have r₁ := eq16181 X0
       have r₂ := eq16140
       grind)
    | exact resolve eq16181 eq16140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16181
  have eq16189 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ y) X0) (σ y))) = X1 ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ y) X0
       have i₂ := eq16184 X0
       grind)
    | exact superpose eq16184 eq9
    | exact resolve eq9 eq16184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16246 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = X1 ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq16189 X0 X1
       have i₂ := eq16184 (M.op (σ y) X0)
       grind)
    | exact superpose eq16184 eq16189
    | exact resolve eq16189 eq16184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16184 eq16189
  have eq16266 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = X1 ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq16246 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16246
  have eq16305 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (σ y)
       have i₂ := eq16266 X0 X0
       grind)
    | exact superpose eq16266 eq9
    | exact resolve eq9 eq16266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16266
  have eq16342 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16305 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq16305
    | (have j1 := eq14 y y
       grind)
    | exact resolve eq16305 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16305
  have eq16404 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq16342 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16342
  have eq16451 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq16404 y X0
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16404
    | (have j0 := eq16404 y x
       grind)
    | exact resolve eq16404 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq16404
  have eq16472 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq16451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16451
  have eq16477 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq16472 y
       grind)
    | (have r₁ := eq16472 X0
       have r₂ := eq16140
       grind)
    | exact resolve eq16472 eq16140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16140 eq16472
  have eq16521 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq16477 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16477
  have eq16522 : y = (M.op y y) := by grind
  clear eq16521
  have eq16525 : y = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16522
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq16522
    | (have j1 := eq14 y y
       grind)
    | exact resolve eq16522 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16527 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq16522
       grind)
    | exact superpose eq16522 eq9
    | exact resolve eq9 eq16522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16528 : y = (k y y) ∨ y = (M.op y y) := by grind
  clear eq16525
  have eq16529 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16527 X0
       have i₂ := eq16522
       grind)
    | exact superpose eq16522 eq16527
    | exact resolve eq16527 eq16522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16527
  have eq16530 : y = (k y y) := by
    first
    | (have r₁ := eq16528
       have r₂ := eq16148 y
       grind)
    | exact resolve eq16528 eq16148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16148 eq16528
  have eq16531 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq16529 X0
       have i₂ := eq16522
       grind)
    | exact superpose eq16522 eq16529
    | exact resolve eq16529 eq16522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16522 eq16529
  have eq16537 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op X0 y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 y X0
       have i₂ := eq16531 (M.op y (M.op X0 y))
       grind)
    | exact superpose eq16531 eq9
    | exact resolve eq9 eq16531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16540 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16537 X0 X1
       have i₂ := eq16531 X0
       grind)
    | exact superpose eq16531 eq16537
    | exact resolve eq16537 eq16531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16537
  have eq16549 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 y
       have i₂ := eq16540 X0 X0
       grind)
    | exact superpose eq16540 eq9
    | exact resolve eq9 eq16540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16540
  have eq16559 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16549 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq16549
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq16549 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16573 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq16559 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16559
  have eq16779 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16573 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq16573
    | (have j0 := eq16573 (σ X0) X1
       grind)
    | exact resolve eq16573 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573
  have eq18361 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16549 (σ X0) X1
       have i₂ := eq16779 X0 X2
       grind)
    | exact superpose eq16779 eq16549
    | (have j1 := eq16779 X0 X2
       grind)
    | exact resolve eq16549 eq16779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16549 eq16779
  have eq18383 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ (M.op X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18361 y X0 X1
       have i₂ := eq16530
       grind)
    | exact superpose eq16530 eq18361
    | (have j0 := eq18361 y X1 x
       grind)
    | exact resolve eq18361 eq16530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16530 eq18361
  have eq18517 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq18383 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18383
  have eq18518 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq18517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18517
  have eq18568 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18518 (σ x)
       grind)
    | exact superpose eq18518 eq16
    | exact resolve eq16 eq18518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18518
  have eq18584 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18568
       have i₂ := eq16531 x
       grind)
    | exact superpose eq16531 eq18568
    | exact resolve eq18568 eq16531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16531 eq18568
  have eq18585 : False := by grind
  exact eq18585

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pxy_pxx_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X0
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
  clear eq24
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
  have eq597 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq609 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq597
       grind)
    | exact superpose eq597 eq41
    | exact resolve eq41 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq610 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq609
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq609
    | exact resolve eq609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq612 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq610
    | exact resolve eq610 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq612 eq601
    | exact resolve eq601 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq612
  have eq629 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq622
       have r₂ := eq27
       grind)
    | exact resolve eq622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq635 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq629 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq629
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq629
       grind)
    | exact resolve eq13 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq637 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq635
  have eq644 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq637 eq142
    | exact resolve eq142 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq637
  have eq647 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq644
    | exact resolve eq644 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq644
  have eq650 : x = (M.op x x) := by
    first
    | (have j1 := eq605 x
       grind)
    | (have r₁ := eq647
       have r₂ := eq605 x
       grind)
    | exact resolve eq647 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq655 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq650
       grind)
    | exact superpose eq650 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq650
       grind)
    | exact resolve eq13 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq650
       grind)
    | exact superpose eq650 eq16
    | exact resolve eq16 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : x = (k x x) := by grind
  clear eq655
  have eq658 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq656 X0
       have i₂ := eq650
       grind)
    | exact superpose eq650 eq656
    | exact resolve eq656 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq660 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq650
       grind)
    | exact superpose eq650 eq658
    | exact resolve eq658 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq658
  have eq663 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq657
       grind)
    | exact superpose eq657 eq40
    | exact resolve eq40 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq657
  have eq666 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq663
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq663
    | exact resolve eq663 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq671 : ∀ X0 : G, X0 ≠ X0 ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq660 X0
       grind)
    | exact superpose eq660 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x X0
       have r₂ := eq660 X0
       grind)
    | exact resolve eq13 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq675 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq806 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq666 eq605
    | (have j0 := eq605 (σ x)
       grind)
    | (have r₁ := eq605 (σ x)
       have r₂ := eq666
       grind)
    | exact resolve eq605 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq666
  have eq807 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq806
  have eq816 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq807 eq16
    | exact resolve eq16 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq807 eq816
    | exact resolve eq816 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq822 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq807 eq819
    | exact resolve eq819 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq819
  have eq830 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq822 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) X0
       have r₂ := eq822 X0
       grind)
    | exact resolve eq13 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq837 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq877 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq675 y
       grind)
    | exact superpose eq675 eq18
    | (have j1 := eq675 y
       grind)
    | exact resolve eq18 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq675
  have eq917 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq41
    | exact resolve eq41 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq877
  have eq918 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq917
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq917
    | exact resolve eq917 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq917
  have eq920 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq918
    | exact resolve eq918 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq918
  have eq1014 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq837 eq26
    | (have j1 := eq837 (σ y)
       grind)
    | exact resolve eq26 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq837
  have eq1049 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq920 eq1014
    | exact resolve eq1014 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq1014
  have eq1057 : False := by grind
  exact eq1057

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq9 X0 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq527 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq544 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq527 (σ X1) (σ X0)
       grind)
    | exact superpose eq527 eq15
    | (have j1 := eq527 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq527 (τ X1) X0
       grind)
    | exact superpose eq527 eq18
    | (have j1 := eq527 (τ X1) X0
       grind)
    | exact resolve eq18 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq527
  have eq558 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq552
    | exact resolve eq552 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq558
    | (have j0 := eq558 X0 X1
       grind)
    | exact resolve eq558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq802 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq544 x y
       grind)
    | exact superpose eq544 eq16
    | (have j1 := eq544 x y
       grind)
    | exact resolve eq16 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq826 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq814 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq814
    | (have j0 := eq814 (τ X1) (τ X0)
       grind)
    | exact resolve eq814 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq834 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq826
    | (have j0 := eq826 X0 X1
       grind)
    | exact resolve eq826 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq836 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq834 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq834
    | (have j0 := eq834 X0 X1
       grind)
    | exact resolve eq834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq837 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq836
    | (have j0 := eq836 X0 X1
       grind)
    | exact resolve eq836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq838 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq837 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq837
    | (have j0 := eq837 X0 X1
       grind)
    | exact resolve eq837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq802
       have i₂ := eq590 y x
       grind)
    | exact superpose eq590 eq802
    | (have j1 := eq590 (σ y) (σ x)
       grind)
    | (have r₁ := eq802
       have r₂ := eq590 y x
       grind)
    | exact resolve eq802 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq802
  have eq927 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq926
  have eq935 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq63 (σ x) X0 (σ y)
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq63
    | exact resolve eq63 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq974 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq63 (σ y) X0 (σ x)
       have i₂ := eq935 (σ y)
       grind)
    | exact superpose eq935 eq63
    | exact resolve eq63 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq1005 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  have eq1026 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq1005
    | exact resolve eq1005 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1206 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq974 (σ y)
       have i₂ := eq1026
       grind)
    | exact superpose eq1026 eq974
    | exact resolve eq974 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq1026
  have eq1217 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) := by grind
  clear eq1206
  have eq1229 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq1217
       grind)
    | exact superpose eq1217 eq10
    | exact resolve eq10 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1270 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1229
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1229
    | exact resolve eq1229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1278 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq838 y y
       have i₂ := eq1270
       grind)
    | exact superpose eq1270 eq838
    | (have j0 := eq838 y y
       grind)
    | (have r₁ := eq838 y y
       have r₂ := eq1270
       grind)
    | exact resolve eq838 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq1270
  have eq1281 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1278
  have eq1288 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq9
    | exact resolve eq9 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1429 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1288 X0
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1288
    | exact resolve eq1288 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1462 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1465 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1462 X0
       have i₂ := eq1281
       grind)
    | exact superpose eq1281 eq1462
    | exact resolve eq1462 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq1462
  have eq1498 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1533 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq1498 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1534 : x = (M.op x y) := by grind
  clear eq1533
  have eq1548 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 x X0 y
       have i₂ := eq1534
       grind)
    | exact superpose eq1534 eq63
    | exact resolve eq63 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1592 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 y X0 x
       have i₂ := eq1548 y
       grind)
    | exact superpose eq1548 eq63
    | exact resolve eq63 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1628 : (k y y) = (M.op y y) := by grind
  have eq1659 : y = (k y y) := by
    first
    | (have i₁ := eq1628
       have i₂ := eq1592 y
       grind)
    | exact superpose eq1592 eq1628
    | exact resolve eq1628 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1669 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq814 y y
       have i₂ := eq1659
       grind)
    | exact superpose eq1659 eq814
    | (have j0 := eq814 y y
       grind)
    | exact resolve eq814 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1659
  have eq1674 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1669
  have eq1752 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (σ y) X0 (σ y)
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq63
    | exact resolve eq63 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1759 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1752 X0
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq1752
    | exact resolve eq1752 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq1766 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1759 X0
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq1759
    | exact resolve eq1759 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674 eq1759
  have eq1792 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1766 (σ x)
       grind)
    | exact superpose eq1766 eq16
    | exact resolve eq16 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq1798 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1792
       have i₂ := eq1592 x
       grind)
    | exact superpose eq1592 eq1792
    | exact resolve eq1792 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592 eq1792
  have eq1799 : False := by grind
  exact eq1799
