import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_pxy_pyy_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq21 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq31 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq33 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq35 X1 X0
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq35 X0 X1
       grind)
    | exact resolve eq39 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq39
  have eq122 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq122 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq122 X0 X0
       have r₂ := eq41 X0 X0
       grind)
    | exact resolve eq122 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq122
  have eq232 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq127 (σ X0) (σ X1)
       grind)
    | exact superpose eq127 eq15
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq127 X0 X1
       grind)
    | exact superpose eq127 eq232
    | exact resolve eq232 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq232
  have eq241 : False := by grind
  exact eq241

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq78 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq80 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq78 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq78 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq83 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq80 (σ X0)
       grind)
    | exact superpose eq80 eq15
    | exact resolve eq15 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq83
    | exact resolve eq83 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq83
  have eq113 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq63
    | exact resolve eq63 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq135 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq12
    | exact resolve eq12 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq135
    | (have j0 := eq135 X0
       grind)
    | exact resolve eq135 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq261 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq265 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X1) (M.op X0 (σ X1))
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq261 X0 (M.op X0 X0)
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq261
    | (have j0 := eq261 X0 (k X0 (M.op X0 X0))
       grind)
    | exact resolve eq261 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq606 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq608 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq612 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq608 X0
       have j1 := eq138 X0
       grind)
    | (have r₁ := eq608 X0
       have r₂ := eq138 X0
       grind)
    | exact resolve eq608 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq608
  have eq624 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq612 X0
       grind)
    | exact superpose eq612 eq10
    | exact resolve eq10 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (M.op X0 X0)) X1
       have i₂ := eq612 X0
       grind)
    | exact superpose eq612 eq15
    | exact resolve eq15 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq663 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq625
    | exact resolve eq625 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq664 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq624 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq624
    | exact resolve eq624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq6390 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X1)
       have i₂ := eq265 X0 X1
       grind)
    | exact superpose eq265 eq12
    | (have j1 := eq265 X1 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq265 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq265 (M.op X0 (σ X1)) X1
       grind)
    | exact resolve eq12 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq6410 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq6390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6390
  have eq6475 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6410 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6410
    | exact resolve eq6410 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6509 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq6410 X0 X1
       grind)
    | exact superpose eq6410 eq23
    | (have j1 := eq6410 X0 X1
       grind)
    | exact resolve eq23 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq6410
  have eq6582 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6509 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6509
    | (have j0 := eq6509 X0 X1
       grind)
    | exact resolve eq6509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6509
  have eq6596 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6475 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq6475
    | (have j0 := eq6475 X0 X1
       grind)
    | exact resolve eq6475 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6475
  have eq6648 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq6596 X1 X0
       grind)
    | exact superpose eq6596 eq11
    | (have j1 := eq6596 X1 X0
       grind)
    | exact resolve eq11 eq6596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6596
  have eq6782 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6648 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq6648
    | (have j0 := eq6648 X0 X1
       grind)
    | exact resolve eq6648 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6648
  have eq6918 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (k X0 (M.op X0 X0)) X1)) ∨ (k (k X0 (M.op X0 X0)) X1) = X1 ∨ (k X0 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq6782 (k X0 (M.op X0 X0)) X1
       grind)
    | exact superpose eq6782 eq663
    | (have j1 := eq6782 (k X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq663 eq6782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq6782
  have eq6973 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k (k X0 (M.op X0 X0)) X1) = X1 ∨ (k X0 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6918 X0 X1
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq6918
    | (have j0 := eq6918 X0 X1
       grind)
    | exact resolve eq6918 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6918
  have eq7005 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6973 X0 X1
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq6973
    | (have j0 := eq6973 X0 X1
       grind)
    | exact resolve eq6973 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6973
  have eq7027 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7005 X0 X1
       have i₂ := eq664 X0
       grind)
    | exact superpose eq664 eq7005
    | (have j0 := eq7005 X0 X1
       grind)
    | exact resolve eq7005 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq7005
  have eq7275 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (τ X1)) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6582 (τ X0) X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq6582
    | (have j0 := eq6582 (τ X1) X0
       grind)
    | exact resolve eq6582 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6582
  have eq7453 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7275 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7275
    | (have j0 := eq7275 X0 X1
       grind)
    | exact resolve eq7275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7275
  have eq7517 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7453 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7453
    | (have j0 := eq7453 X0 X1
       grind)
    | exact resolve eq7453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7453
  have eq7809 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq7517 X0 X1
       grind)
    | exact superpose eq7517 eq11
    | (have j1 := eq7517 X0 X1
       grind)
    | exact resolve eq11 eq7517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7517
  have eq7944 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7809 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq7809
    | (have j0 := eq7809 X0 X1
       grind)
    | exact resolve eq7809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7809
  have eq8078 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7944 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7944
    | (have j0 := eq7944 (τ (σ (k X0 X1))) (τ (σ X1))
       grind)
    | exact resolve eq7944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7944
  have eq8273 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8078 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8078
    | (have j0 := eq8078 X0 X1
       grind)
    | exact resolve eq8078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8078
  have eq8284 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8273 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq8273
    | (have j0 := eq8273 X0 X1
       grind)
    | exact resolve eq8273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8273
  have eq9388 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8284 x y
       grind)
    | exact superpose eq8284 eq16
    | (have j1 := eq8284 x y
       grind)
    | exact resolve eq16 eq8284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8284
  have eq9462 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9388
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq9388
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq9388
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq9388
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq9388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9463 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq9388
       have i₂ := eq7027 x y
       grind)
    | exact superpose eq7027 eq9388
    | (have j1 := eq7027 x y
       grind)
    | (have r₁ := eq9388
       have r₂ := eq7027 x y
       grind)
    | (have r₁ := eq9388
       have r₂ := eq7027 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq9388
       have r₂ := eq7027 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq9388 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7027 eq9388
  have eq9466 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq9463
  have eq9467 : x = y ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq9466
  have eq9468 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq9462
  have eq9469 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq9468
  have eq9472 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9467
       grind)
    | exact superpose eq9467 eq16
    | exact resolve eq16 eq9467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9467
  have eq9473 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9472
       have r₂ := eq94 x
       grind)
    | exact resolve eq9472 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9472
  have eq9478 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq606 x y
       have i₂ := eq9473
       grind)
    | exact superpose eq9473 eq606
    | (have j0 := eq606 x y
       grind)
    | exact resolve eq606 eq9473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq9473
  have eq9485 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9478
  have eq9486 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq9485
  have eq9491 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9469
       grind)
    | exact superpose eq9469 eq16
    | exact resolve eq16 eq9469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9469
  have eq9492 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9491
       have r₂ := eq94 x
       grind)
    | exact resolve eq9491 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9491
  have eq9511 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9486
       grind)
    | exact superpose eq9486 eq16
    | exact resolve eq16 eq9486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9486
  have eq9535 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9511
       have i₂ := eq9492
       grind)
    | exact superpose eq9492 eq9511
    | exact resolve eq9511 eq9492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9492 eq9511
  have eq9536 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq9535
  have eq9537 : (σ x) = (σ y) := by grind
  clear eq9536
  have eq9538 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9537
       grind)
    | exact superpose eq9537 eq16
    | exact resolve eq16 eq9537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9539 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9537
       grind)
    | exact superpose eq9537 eq10
    | exact resolve eq10 eq9537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9537
  have eq9599 : x = y := by
    first
    | (have i₁ := eq9539
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9539
    | exact resolve eq9539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9539
  have eq9600 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9538
       have i₂ := eq94 x
       grind)
    | exact superpose eq94 eq9538
    | exact resolve eq9538 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq9538
  have eq9601 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9600
       have i₂ := eq9599
       grind)
    | exact superpose eq9599 eq9600
    | exact resolve eq9600 eq9599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9599 eq9600
  have eq9602 : False := by grind
  exact eq9602

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pxy_x_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq74 (σ X0)
       grind)
    | exact superpose eq74 eq15
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq74 (τ X0)
       grind)
    | exact superpose eq74 eq32
    | exact resolve eq32 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq86 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq79
    | exact resolve eq79 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq77
    | exact resolve eq77 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq77
  have eq106 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq63
    | exact resolve eq63 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq585 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq560
    | (have j0 := eq560 X0 X1
       grind)
    | exact resolve eq560 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq599 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq88 X1
       grind)
    | exact superpose eq88 eq585
    | (have j0 := eq585 X0 X1
       grind)
    | exact resolve eq585 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq585
  have eq3484 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq599
    | exact resolve eq599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq3563 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3484 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq3484
    | (have j0 := eq3484 X0 X1
       grind)
    | exact resolve eq3484 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484
  have eq3587 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3563 X0 X1
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq3563
    | (have j0 := eq3563 X0 X1
       grind)
    | exact resolve eq3563 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563
  have eq3594 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3587 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3587
    | (have j0 := eq3587 X0 X1
       grind)
    | exact resolve eq3587 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq3599 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3594 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq3594 (σ X1) X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq3594 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq3594 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594
  have eq3603 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3599 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3599
    | (have j0 := eq3599 X1 (τ X0)
       grind)
    | exact resolve eq3599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3624 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3599 (σ X1) X0
       grind)
    | exact superpose eq3599 eq15
    | (have j1 := eq3599 (σ X1) X0
       grind)
    | exact resolve eq15 eq3599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599
  have eq3684 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3603 X0 X1
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq3603
    | (have j0 := eq3603 X0 X1
       grind)
    | exact resolve eq3603 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq3603
  have eq3685 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3684 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3684
    | (have j0 := eq3684 X0 X1
       grind)
    | exact resolve eq3684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3684
  have eq3706 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq3685 X0 (τ X1)
       grind)
    | exact superpose eq3685 eq19
    | (have j1 := eq3685 X0 (τ X1)
       grind)
    | exact resolve eq19 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3685
  have eq4381 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3706 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3706
    | exact resolve eq3706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706
  have eq4460 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4381 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4381
    | (have j0 := eq4381 X0 X1
       grind)
    | exact resolve eq4381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4381
  have eq4886 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3624 x y
       grind)
    | exact superpose eq3624 eq16
    | (have j1 := eq3624 x y
       grind)
    | exact resolve eq16 eq3624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3624
  have eq5002 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4886
       have i₂ := eq4460 y x
       grind)
    | exact superpose eq4460 eq4886
    | (have j1 := eq4460 y x
       grind)
    | (have r₁ := eq4886
       have r₂ := eq4460 y x
       grind)
    | exact resolve eq4886 eq4460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4460 eq4886
  have eq5003 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq5002
  have eq5008 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq5003
       grind)
    | exact superpose eq5003 eq63
    | exact resolve eq63 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5013 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq5003
       grind)
    | exact superpose eq5003 eq106
    | exact resolve eq106 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5003
  have eq5040 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5013
       grind)
    | exact superpose eq5013 eq16
    | exact resolve eq16 eq5013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5013
  have eq5070 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5040
       have i₂ := eq5008
       grind)
    | exact superpose eq5008 eq5040
    | exact resolve eq5040 eq5008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5008 eq5040
  have eq5071 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq5070
  have eq5072 : (σ y) = (σ (M.op x x)) := by grind
  clear eq5071
  have eq5075 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq5072
       grind)
    | exact superpose eq5072 eq106
    | exact resolve eq106 eq5072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq5081 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5072
       grind)
    | exact superpose eq5072 eq10
    | exact resolve eq10 eq5072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5072
  have eq5135 : y = (M.op x x) := by
    first
    | (have i₁ := eq5081
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5081
    | exact resolve eq5081 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5081
  have eq5138 : x = (M.op x y) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq5135
       grind)
    | exact superpose eq5135 eq63
    | exact resolve eq63 eq5135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq5135
  have eq5174 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5075
       grind)
    | exact superpose eq5075 eq16
    | exact resolve eq16 eq5075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5075
  have eq5186 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5174
       have i₂ := eq5138
       grind)
    | exact superpose eq5138 eq5174
    | exact resolve eq5174 eq5138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5138 eq5174
  have eq5187 : False := by grind
  exact eq5187

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyy_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq73 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq74 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq304 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op (M.op X1 X1) X0) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq314 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq319 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq304 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq320 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq321 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq315 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq315 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq315 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq335 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq321 (σ X0)
       grind)
    | exact superpose eq321 eq15
    | exact resolve eq15 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq335 X0
       have i₂ := eq321 X0
       grind)
    | exact superpose eq321 eq335
    | exact resolve eq335 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq335
  have eq403 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 (σ X0)
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq74
    | exact resolve eq74 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq403 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq403
    | exact resolve eq403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq410 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq406 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq406
    | exact resolve eq406 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq406
  have eq489 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq320 (σ X1) (σ X0)
       grind)
    | exact superpose eq320 eq15
    | (have j1 := eq320 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq320 X1 (τ X0)
       grind)
    | exact superpose eq320 eq18
    | (have j1 := eq320 X1 (τ X0)
       grind)
    | exact resolve eq18 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq320
  have eq506 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 X1
       have i₂ := eq354 X1
       grind)
    | exact superpose eq354 eq489
    | (have j0 := eq489 X0 X1
       grind)
    | exact resolve eq489 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq489
  have eq579 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq497 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq497
    | exact resolve eq497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq635 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq579
    | (have j0 := eq579 X0 X1
       grind)
    | exact resolve eq579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq1384 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq506 x y
       grind)
    | exact superpose eq506 eq16
    | (have j1 := eq506 x y
       grind)
    | exact resolve eq16 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq1475 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1384
       have i₂ := eq635 x y
       grind)
    | exact superpose eq635 eq1384
    | (have j1 := eq635 x y
       grind)
    | (have r₁ := eq1384
       have r₂ := eq635 x y
       grind)
    | exact resolve eq1384 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq1384
  have eq1476 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1475
  have eq1484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq410
    | exact resolve eq410 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1504 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1484
       have r₂ := eq16
       grind)
    | exact resolve eq1484 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1511 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1504
       grind)
    | exact superpose eq1504 eq10
    | exact resolve eq10 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1558 : x = (M.op y y) := by
    first
    | (have i₁ := eq1511
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1511
    | exact resolve eq1511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq1558
       grind)
    | exact superpose eq1558 eq410
    | exact resolve eq410 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq1558
  have eq1586 : False := by grind
  exact eq1586

/-- `Equation1052`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyy_y_pxx_pxx_pxy_Equation1052 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1052 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1052.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X1)) = X0 := by
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq177 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq177 X0 (M.op X0 X0)
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1053 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1054
       have i₂ := eq1066 sF2
       grind)
    | exact superpose eq1066 eq1054
    | exact resolve eq1054 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1073 : (M.op x y) ≠ (k x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq1053
       have i₂ := eq1066 x
       grind)
    | exact superpose eq1066 eq1053
    | exact resolve eq1053 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1081 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq1066 sF2
       grind)
    | exact superpose eq1066 eq1072
    | exact resolve eq1072 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1082 : (M.op x y) ≠ (k x x) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq1073
       have i₂ := eq1066 x
       grind)
    | exact superpose eq1066 eq1073
    | exact resolve eq1073 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1092 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
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
  have eq1093 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1152 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1093
       have i₂ := eq1066 sF3
       grind)
    | exact superpose eq1066 eq1093
    | exact resolve eq1093 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1153 : y = (k y y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1092
       have i₂ := eq1066 y
       grind)
    | exact superpose eq1066 eq1092
    | exact resolve eq1092 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1175 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1152
       have i₂ := eq1066 sF2
       grind)
    | exact superpose eq1066 eq1152
    | exact resolve eq1152 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1176 : (M.op x y) = (k x y) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1153
       have i₂ := eq1066 x
       grind)
    | exact superpose eq1066 eq1153
    | exact resolve eq1153 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1227 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq1066 (M.op X0 X0)
       grind)
    | exact superpose eq1066 eq200
    | exact resolve eq200 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq1228 : ∀ X0 X1 : G, (M.op X1 (k (k X0 X0) (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1227 X0 X1
       have i₂ := eq1066 X0
       grind)
    | exact superpose eq1066 eq1227
    | exact resolve eq1227 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq1227
  have eq1862 : ∀ X0 X1 : G, (M.op X1 (k (σ (k X0 X0)) (σ (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1228 (σ X1) X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq1228
    | exact resolve eq1228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1922 : ∀ X0 X1 : G, (M.op X1 (σ (k (k X0 X0) (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1862 X0 X1
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq1862
    | exact resolve eq1862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq5435 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1176
       grind)
    | exact superpose eq1176 eq41
    | exact resolve eq41 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq5436 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq5435
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5435
    | exact resolve eq5435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5435
  have eq5438 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20 eq5436
    | exact resolve eq5436 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5436
  have eq99375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq5438 eq1175
    | exact resolve eq1175 eq5438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99386 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq99375
       have r₂ := eq27
       grind)
    | exact resolve eq99375 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99375
  have eq99394 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq99386 eq1081
    | (have r₁ := eq1081
       have r₂ := eq99386
       grind)
    | exact resolve eq1081 eq99386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq99386
  have eq99512 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by grind
  clear eq99394
  have eq99551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq5438 eq99512
    | exact resolve eq99512 eq5438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5438 eq99512
  have eq99561 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq99551
       have r₂ := eq27
       grind)
    | exact resolve eq99551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99551
  have eq99571 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq99561 eq153
    | exact resolve eq153 eq99561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99561
  have eq99789 : y = (k y y) ∨ y = (k y y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq32 eq99571
    | exact resolve eq99571 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99571
  have eq99790 : (M.op x y) = (k x x) ∨ y = (k y y) := by grind
  clear eq99789
  have eq99895 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq1082
       have i₂ := eq99790
       grind)
    | exact superpose eq99790 eq1082
    | (have r₁ := eq1082
       have r₂ := eq99790
       grind)
    | exact resolve eq1082 eq99790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq99897 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq99790
       grind)
    | exact superpose eq99790 eq40
    | exact resolve eq40 eq99790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq99790
  have eq100012 : (M.op x y) = (k x y) ∨ y = (k y y) := by grind
  clear eq99895
  have eq100053 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq99897
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq99897
    | exact resolve eq99897 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99897
  have eq100085 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq100053
    | exact resolve eq100053 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100053
  have eq100103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq100012
       grind)
    | exact superpose eq100012 eq41
    | exact resolve eq41 eq100012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100012
  have eq100109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq100103
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100103
    | exact resolve eq100103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100103
  have eq100114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq100109
    | exact resolve eq100109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100109
  have eq100324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq100114 eq1175
    | exact resolve eq1175 eq100114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq100114
  have eq100334 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq100324
       have r₂ := eq27
       grind)
    | exact resolve eq100324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100324
  have eq100341 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq100085 eq100334
    | exact resolve eq100334 eq100085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100085 eq100334
  have eq100344 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq100341
       have r₂ := eq27
       grind)
    | exact resolve eq100341 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100341
  have eq100351 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq100344 eq153
    | exact resolve eq153 eq100344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq100344
  have eq100569 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq100351
    | exact resolve eq100351 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq100351
  have eq100570 : y = (k y y) := by grind
  clear eq100569
  have eq100676 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq100570
       grind)
    | exact superpose eq100570 eq41
    | exact resolve eq41 eq100570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100683 : ∀ X0 : G, (M.op X0 (k y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1228 y x
       have i₂ := eq100570
       grind)
    | exact superpose eq100570 eq1228
    | exact resolve eq1228 eq100570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq100711 : ∀ X0 : G, (M.op X0 (σ (k y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1922 y x
       have i₂ := eq100570
       grind)
    | exact superpose eq100570 eq1922
    | exact resolve eq1922 eq100570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq100865 : ∀ X0 : G, (M.op X0 (k (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq100711 X0
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq100711
    | exact resolve eq100711 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq100711
  have eq100890 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq100683 X0
       have i₂ := eq100570
       grind)
    | exact superpose eq100570 eq100683
    | exact resolve eq100683 eq100570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100570 eq100683
  have eq100894 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq100676
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq100676
    | exact resolve eq100676 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100676
  have eq100968 : ∀ X0 : G, (M.op X0 (k (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq100865 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq100865
    | (have j0 := eq100865 X0
       grind)
    | exact resolve eq100865 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq100865
  have eq101041 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq100894 eq100968
    | exact resolve eq100968 eq100894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100894 eq100968
  have eq101240 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq100890 x
       grind)
    | exact superpose eq100890 eq18
    | (have j1 := eq100890 x
       grind)
    | exact resolve eq18 eq100890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq100890
  have eq101516 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq101240
       grind)
    | exact superpose eq101240 eq22
    | exact resolve eq22 eq101240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq101240
  have eq101696 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq101516 eq20
    | exact resolve eq20 eq101516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq101516
  have eq102978 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101041 eq26
    | (have j1 := eq101041 (σ x)
       grind)
    | exact resolve eq26 eq101041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq101041
  have eq103258 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq102978 eq27
    | exact resolve eq27 eq102978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq102978
  have eq103357 : False := by grind
  exact eq103357

/-- `Equation1052`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pxy_pxx_pxy_Equation1052 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1052 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1052.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X1)) = X0 := by
    intro X0 X1 X2
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
  have eq52 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = X1 := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq44
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq44 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq97 eq68
    | (have j0 := eq68 x (σ y)
       grind)
    | exact resolve eq68 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq650 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq649
    | exact resolve eq649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq653 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq650
       have r₂ := eq27
       grind)
    | exact resolve eq650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq656 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq653 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq653
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq653
       grind)
    | exact resolve eq13 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq661 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq656
  have eq683 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq661 eq103
    | exact resolve eq103 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq661
  have eq687 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq683
    | exact resolve eq683 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq683
  have eq690 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq68 y y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq691 : y = (M.op y y) := by grind
  clear eq690
  have eq752 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq691
       grind)
    | exact resolve eq13 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 y X0
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq52
    | exact resolve eq52 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : y = (k y y) := by grind
  clear eq752
  have eq758 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq754 X0
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq754
    | exact resolve eq754 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq754
  have eq768 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq75
    | exact resolve eq75 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq757
  have eq772 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq768
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq768
    | exact resolve eq768 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq768
  have eq836 : x = (M.op x y) := by
    first
    | (have i₁ := eq758 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq758
    | (have j0 := eq758 x
       grind)
    | exact resolve eq758 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq758
  have eq857 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq836 eq20
    | exact resolve eq20 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq836
  have eq876 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq857
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq857
    | exact resolve eq857 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq857
  have eq878 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq876 eq26
    | exact resolve eq26 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq876
  have eq899 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq772 eq68
    | (have j0 := eq68 x (σ y)
       grind)
    | exact resolve eq68 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq772
  have eq900 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq899
  have eq927 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq900 eq52
    | exact resolve eq52 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq941 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq900 eq927
    | exact resolve eq927 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq927
  have eq973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq941 eq878
    | exact resolve eq878 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq941
  have eq977 : False := by grind
  exact eq977

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_x_pyx_y_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq16 X0 X2 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq188 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq985 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq986 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1031 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1031 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1062 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq985
       grind)
    | exact superpose eq985 eq40
    | exact resolve eq40 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1063 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1062
    | exact resolve eq1062 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1065 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1063
    | exact resolve eq1063 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1065 eq986
    | exact resolve eq986 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq1065
  have eq1080 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1073
       have r₂ := eq27
       grind)
    | exact resolve eq1073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1086 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1080 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1080
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1080
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1080
       grind)
    | exact resolve eq13 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1090 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1086
  have eq1098 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1090 eq141
    | exact resolve eq141 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1090
  have eq1101 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1098
    | exact resolve eq1098 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1098
  have eq1104 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1033 x
       grind)
    | (have r₁ := eq1101
       have r₂ := eq1033 x
       grind)
    | exact resolve eq1101 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1109 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1104
       grind)
    | exact superpose eq1104 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1104
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1104
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1104
       grind)
    | exact resolve eq13 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq1104
       grind)
    | exact superpose eq1104 eq16
    | exact resolve eq16 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1109
  have eq1115 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1104 eq1110
    | exact resolve eq1110 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1117 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1104 eq1115
    | exact resolve eq1115 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1115
  have eq1120 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1113
       grind)
    | exact superpose eq1113 eq39
    | exact resolve eq39 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1123 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1120
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1120
    | exact resolve eq1120 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1128 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1117 X0
       grind)
    | exact superpose eq1117 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1117 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1117 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1117 X0
       grind)
    | exact resolve eq13 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1140 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1154 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1123 eq1033
    | (have j0 := eq1033 (σ x)
       grind)
    | (have r₁ := eq1033 (σ x)
       have r₂ := eq1123
       grind)
    | exact resolve eq1033 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1155 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1154
  have eq1163 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1155 eq16
    | exact resolve eq16 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1155 eq1163
    | exact resolve eq1163 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1169 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1155 eq1167
    | exact resolve eq1167 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1167
  have eq1174 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1169 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1169 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1169 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1169 X0
       grind)
    | exact resolve eq13 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1186 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1174 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1244 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1140 y
       grind)
    | exact superpose eq1140 eq18
    | (have j1 := eq1140 y
       grind)
    | exact resolve eq18 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1312 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1244
       grind)
    | exact superpose eq1244 eq39
    | exact resolve eq39 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1244
  have eq1313 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1312
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1312
    | exact resolve eq1312 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1315 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1313
    | exact resolve eq1313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1433 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1186 eq26
    | (have j1 := eq1186 (σ y)
       grind)
    | exact resolve eq26 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1315 eq1433
    | exact resolve eq1433 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq1433
  have eq1506 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1489
       have r₂ := eq27
       grind)
    | exact resolve eq1489 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1515 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1506 eq188
    | exact resolve eq188 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq1506
  have eq1542 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1542_12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
      intro X0 X1 X2
      grind
    have f1542_13 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
      intro X0
      grind
    have f1542_21 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f1542_22 : x ≠ (M.op x y) := by grind
    have f1542_23 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f1542_13 X0
         grind)
      | (have r₁ := f1542_13 X0
         have r₂ := f1542_22
         grind)
      | exact resolve f1542_13 f1542_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1542_72 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f1542_12 (σ y) X0 (σ x)
         have i₂ := f1542_23 (σ y)
         grind)
      | exact superpose f1542_23 f1542_12
      | exact resolve f1542_12 f1542_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1542_85 : X0 ≠ X0 := by
      first
      | (have i₁ := f1542_21
         have i₂ := f1542_72 X0
         grind)
      | exact superpose f1542_72 f1542_21
      | (have r₁ := f1542_21
         have r₂ := f1542_72 X0
         grind)
      | exact resolve f1542_21 f1542_72
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1542_86 : False := by grind
    exact f1542_86
  clear eq1515
  have eq2005 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1542 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1542 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1542 X0
       grind)
    | exact resolve eq13 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2024 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2103 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2024 eq1542
    | exact resolve eq1542 eq2024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542 eq2024
  have eq2104 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2103
  have eq2172 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2104 eq152
    | exact resolve eq152 eq2104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2104
  have eq2175 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2172
    | exact resolve eq2172 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2172
  have eq2180 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1033 y
       have i₂ := eq2175
       grind)
    | exact superpose eq2175 eq1033
    | (have j0 := eq1033 y
       grind)
    | (have r₁ := eq1033 y
       have r₂ := eq2175
       grind)
    | exact resolve eq1033 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2181 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq2180
  have eq2190 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq2181
       grind)
    | exact superpose eq2181 eq16
    | exact resolve eq16 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2194 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2181 eq2190
    | exact resolve eq2190 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2198 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2181 eq2194
    | exact resolve eq2194 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181 eq2194
  have eq2225 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2198 x
       grind)
    | exact superpose eq2198 eq18
    | (have j1 := eq2198 x
       grind)
    | exact resolve eq18 eq2198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2198
  have eq2236 : x = (M.op x y) := by grind
  clear eq2225
  have eq2244 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq2236
       grind)
    | exact superpose eq2236 eq22
    | exact resolve eq22 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2249 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq2236
       grind)
    | exact superpose eq2236 eq183
    | exact resolve eq183 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq2236
  have eq2255 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2244 eq20
    | exact resolve eq20 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2244
  have eq2550 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq2249 eq177
    | exact resolve eq177 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2249
  have eq2613 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2550 X0
       grind)
    | exact superpose eq2550 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2550 X0
       grind)
    | exact resolve eq13 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2633 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq2613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613
  have eq2713 : y = (k y y) := by
    first
    | (have i₁ := eq2550 y
       have i₂ := eq2633 y
       grind)
    | exact superpose eq2633 eq2550
    | exact resolve eq2550 eq2633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550 eq2633
  have eq2771 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq2713
       grind)
    | exact superpose eq2713 eq40
    | exact resolve eq40 eq2713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2713
  have eq2774 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2771
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2771
    | exact resolve eq2771 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2771
  have eq2813 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2774 eq1033
    | (have j0 := eq1033 (σ y)
       grind)
    | (have r₁ := eq1033 (σ y)
       have r₂ := eq2774
       grind)
    | exact resolve eq1033 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq2774
  have eq2814 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2813
  have eq2874 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq2814 eq16
    | exact resolve eq16 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2878 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq2814 eq2874
    | exact resolve eq2874 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874
  have eq2882 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq2814 eq2878
    | exact resolve eq2878 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814 eq2878
  have eq2912 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2882 eq26
    | (have j1 := eq2882 (σ x)
       grind)
    | exact resolve eq26 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2882
  have eq2929 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2912 eq27
    | exact resolve eq27 eq2912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2912
  have eq2938 : False := by grind
  exact eq2938

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq714 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq728 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq715 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq741 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq728 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq728 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq728 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq728 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq742 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq714 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq714 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq714 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq758 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq759 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq758 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq760 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq742
    | (have j0 := eq742 X0 X1
       grind)
    | exact resolve eq742 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq761 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq760 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq766 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq761 X0 X1
       have j1 := eq759 X0 X1
       grind)
    | (have r₁ := eq761 X0 X1
       have r₂ := eq759 X0 X1
       grind)
    | exact resolve eq761 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq761
  have eq767 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq766 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq766
    | exact resolve eq766 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq766 x y
       grind)
    | exact superpose eq766 eq16
    | exact resolve eq16 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq937 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq767 X0 (τ X1)
       grind)
    | exact superpose eq767 eq18
    | exact resolve eq18 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq767
  have eq954 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq937 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq937
    | exact resolve eq937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq962 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq954
    | exact resolve eq954 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq974 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq782
       have i₂ := eq962 x y
       grind)
    | exact superpose eq962 eq782
    | exact resolve eq782 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq962
  have eq975 : False := by grind
  exact eq975
