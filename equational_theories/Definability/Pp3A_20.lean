import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxx_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq59 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq256 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq12
    | (have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq267 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq256 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq276 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq267
    | (have j0 := eq267 X0 X1
       grind)
    | exact resolve eq267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq277 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq331 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq277
    | exact resolve eq277 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq277 x y
       grind)
    | exact superpose eq277 eq16
    | (have j1 := eq277 x y
       grind)
    | exact resolve eq16 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq355 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq331
    | (have j0 := eq331 X0 X1
       grind)
    | exact resolve eq331 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq331
  have eq393 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq355
    | exact resolve eq355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq489 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq337
       have i₂ := eq393 x y
       grind)
    | exact superpose eq393 eq337
    | (have j1 := eq393 (σ x) (σ y)
       grind)
    | (have r₁ := eq337
       have r₂ := eq393 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq337
       have r₂ := eq393 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq337 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq393
  have eq492 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq489
  have eq524 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq492
       grind)
    | exact superpose eq492 eq10
    | exact resolve eq10 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq559 : x = y ∨ x = y := by
    first
    | (have i₁ := eq524
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq524
    | exact resolve eq524 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq560 : x = y := by grind
  clear eq559
  have eq562 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq560
       grind)
    | exact superpose eq560 eq16
    | exact resolve eq16 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq563 : False := by grind
  exact eq563

/-- `Equation3926`: `x ◇ y = (x ◇ (y ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pyx_Equation3926 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3926 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3926.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X0)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq109 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (σ X0) (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (τ X0) (τ X0) x
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq110
    | exact resolve eq110 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq135 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 (M.op X0 X1) X1
       have i₂ := eq110 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq111
    | exact resolve eq111 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq168 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 (M.op X0 X1) X1
       have i₂ := eq110 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq112
    | exact resolve eq112 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq700 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq702 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3279 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq700 x y
       grind)
    | exact superpose eq700 eq16
    | (have j1 := eq700 x y
       grind)
    | exact resolve eq16 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq15093 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq702
    | exact resolve eq702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq15231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15093 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq15093
    | (have j0 := eq15093 X0 X1
       grind)
    | exact resolve eq15093 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15093
  have eq34960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3279
       have i₂ := eq15231 y x
       grind)
    | exact superpose eq15231 eq3279
    | (have j1 := eq15231 (σ y) (σ x)
       grind)
    | (have r₁ := eq3279
       have r₂ := eq15231 y x
       grind)
    | (have r₁ := eq3279
       have r₂ := eq15231 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3279
       have r₂ := eq15231 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3279 eq15231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279 eq15231
  have eq34961 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq34960
  have eq252738 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34961
       grind)
    | exact superpose eq34961 eq16
    | exact resolve eq16 eq34961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34961
  have eq252751 : (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq252738
       have r₂ := eq22 x
       grind)
    | exact resolve eq252738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252738
  have eq252753 : y = (τ (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq252751
       grind)
    | exact superpose eq252751 eq10
    | exact resolve eq10 eq252751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252751
  have eq252868 : x = y ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq252753
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq252753
    | exact resolve eq252753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252753
  have eq252870 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq252868
       grind)
    | exact superpose eq252868 eq16
    | exact resolve eq16 eq252868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252868
  have eq252883 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq252870
       have r₂ := eq22 x
       grind)
    | exact resolve eq252870 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq252870
  have eq252913 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq110 y x x
       have i₂ := eq252883
       grind)
    | exact superpose eq252883 eq110
    | exact resolve eq110 eq252883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq252883
  have eq253129 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (τ (σ x)) X0) ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (σ y) (σ x) x
       have i₂ := eq252913 X0
       grind)
    | exact superpose eq252913 eq168
    | (have j1 := eq252913 X1
       grind)
    | exact resolve eq168 eq252913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq252913
  have eq253334 : ∀ X0 X1 : G, x = (M.op x X0) ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq253129 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq253129
    | (have j0 := eq253129 X0 X0
       grind)
    | exact resolve eq253129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253129
  have eq253861 : ∀ X0 : G, x ≠ x ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq253334 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253334
  have eq253862 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq253861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253861
  have eq254149 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq135 x x x
       have i₂ := eq253862 x
       grind)
    | exact superpose eq253862 eq135
    | exact resolve eq135 eq253862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq254443 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq254149 (σ y)
       grind)
    | exact superpose eq254149 eq16
    | exact resolve eq16 eq254149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254149
  have eq255040 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq254443
       have i₂ := eq253862 y
       grind)
    | exact superpose eq253862 eq254443
    | exact resolve eq254443 eq253862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253862 eq254443
  have eq255041 : False := by grind
  exact eq255041

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X2
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq81 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq82 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq99 y x
       grind)
    | exact superpose eq99 eq76
    | (have j1 := eq99 y x
       grind)
    | exact resolve eq76 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq99
    | (have j0 := eq99 (σ y) (σ x)
       grind)
    | exact resolve eq99 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq129
       have r₂ := eq27
       grind)
    | exact resolve eq129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq134 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq132
    | exact resolve eq132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq27
    | exact resolve eq27 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq82
    | (have r₁ := eq82
       have r₂ := eq134
       grind)
    | exact resolve eq82 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq134
  have eq741 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq740
  have eq744 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq741 eq125
    | exact resolve eq125 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq748 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq744
  have eq753 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq748
       have r₂ := eq136
       grind)
    | exact resolve eq748 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq748
  have eq763 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq753 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq753
       grind)
    | exact resolve eq13 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq766 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq2216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq766 eq125
    | exact resolve eq125 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq766
  have eq2219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2216
  have eq2226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2219
    | exact resolve eq2219 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219
  have eq2228 : y = (M.op x y) := by
    first
    | (have r₁ := eq2226
       have r₂ := eq27
       grind)
    | exact resolve eq2226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq2230 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2228 eq20
    | exact resolve eq20 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2234 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq2228 eq81
    | (have r₁ := eq81
       have r₂ := eq2228
       grind)
    | exact resolve eq81 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2238 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq2234
  have eq2244 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2230
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2230
    | exact resolve eq2230 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2247 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2244 eq26
    | exact resolve eq26 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2734 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq2238
       grind)
    | exact superpose eq2238 eq76
    | exact resolve eq76 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq2238
  have eq2741 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2244 eq2734
    | exact resolve eq2734 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq2743 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2741
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2741
    | exact resolve eq2741 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq2744 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2244 eq2743
    | exact resolve eq2743 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq3013 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2744 eq99
    | (have j0 := eq99 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq99 eq2744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744
  have eq3014 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq3013
  have eq3016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2247 eq3014
    | exact resolve eq3014 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014
  have eq3019 : x = (M.op x x) := by
    first
    | (have r₁ := eq3016
       have r₂ := eq27
       grind)
    | exact resolve eq3016 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3034 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq56 x x x
       have i₂ := eq3019
       grind)
    | exact superpose eq3019 eq56
    | exact resolve eq56 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq3040 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq3034 X0
       have i₂ := eq3019
       grind)
    | exact superpose eq3019 eq3034
    | exact resolve eq3034 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019 eq3034
  have eq3053 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3040 y
       grind)
    | exact superpose eq3040 eq18
    | (have j1 := eq3040 y
       grind)
    | exact resolve eq18 eq3040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3055 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq3040 x
       grind)
    | exact superpose eq3040 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq3040 x
       grind)
    | exact resolve eq13 eq3040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3069 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq3055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq3082 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq3069 X0
       have i₂ := eq3040 X0
       grind)
    | exact superpose eq3040 eq3069
    | exact resolve eq3069 eq3040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040 eq3069
  have eq3084 : x = y := by
    first
    | exact superpose eq2228 eq3053
    | exact resolve eq3053 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228 eq3053
  have eq3101 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3084
       grind)
    | exact superpose eq3084 eq24
    | exact resolve eq24 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3084
  have eq3121 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2244 eq3101
    | exact resolve eq3101 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244 eq3101
  have eq3130 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3121
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3121
    | exact resolve eq3121 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121
  have eq3160 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3130 eq2247
    | exact resolve eq2247 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq3198 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq3082 (τ X0)
       grind)
    | exact superpose eq3082 eq34
    | exact resolve eq34 eq3082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3082
  have eq3200 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3198 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3198
    | (have j0 := eq3198 X0
       grind)
    | exact resolve eq3198 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3198
  have eq3204 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3130 eq3200
    | exact resolve eq3200 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130 eq3200
  have eq3216 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3204 X0
       have i₂ := eq99 X0 sF1
       grind)
    | exact superpose eq99 eq3204
    | (have j1 := eq99 X0 (σ (M.op x y))
       grind)
    | exact resolve eq3204 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq3204
  have eq3958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3160 eq3216
    | exact resolve eq3216 eq3160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3160 eq3216
  have eq3977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq3958
  have eq3993 : False := by grind
  exact eq3993

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyy_x_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X1 (M.op x x) x X4
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq16 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq186 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have r₁ := eq13 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ≠ X1 ∨ (k X1 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq179 X0 X1
       grind)
    | (have i₁ := eq13 X1 (M.op (M.op (σ x) (σ y)) (σ y))
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1)
       have r₂ := eq179 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq180 X3 x X4
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq180 X0 (M.op X0 X0) X4
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq180 x X1 X3
       have i₂ := eq179 x X0
       grind)
    | (have i₁ := eq180 (M.op (M.op (σ x) (σ y)) (σ y)) X1 x
       have i₂ := eq179 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq179 eq180
    | exact resolve eq180 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op x y) y) X3) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq178 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq179 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ X2 ∨ (M.op (M.op X0 X0) X1) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq180 X0 X1 x
       grind)
    | (have i₁ := eq13 x (M.op X0 X0)
       have i₂ := eq180 X0 X1 x
       grind)
    | exact superpose eq180 eq13
    | (have r₁ := eq13 (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x)
       have r₂ := eq180 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 x (M.op X1 X1)
       have r₂ := eq180 X1 X1 x
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq180 X1 X0 X2
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq180 X0 X1 x
       grind)
    | exact superpose eq180 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X0) x) (M.op (M.op X0 X0) x)
       have r₂ := eq180 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 x (M.op X1 X1)
       have r₂ := eq180 X1 X1 x
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X1 X2 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (k X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq294 x X1 X2
       grind)
    | (have r₁ := eq294 x X1 X2
       have r₂ := eq181 x X1
       grind)
    | (have r₁ := eq294 X1 x X2
       have r₂ := eq181 x X1
       grind)
    | exact resolve eq294 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq477 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq1298 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq200 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1359 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq179 X0 X1
       grind)
    | (have i₁ := eq11 X1 (M.op (M.op (σ x) (σ y)) (σ y))
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq11
    | exact resolve eq11 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1360 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 X2) ∨ (M.op (M.op X0 X0) X1) = X2 ∨ (M.op (M.op X0 X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq180 X0 X1 x
       grind)
    | (have i₁ := eq11 x (M.op X0 X0)
       have i₂ := eq180 X0 X1 x
       grind)
    | exact superpose eq180 eq11
    | exact resolve eq11 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1362 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq1385 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1362 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1466 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 X2) ∨ (M.op (M.op X0 X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1360 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1467 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1359 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq1476 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1464 X0 X1
       have j1 := eq200 X0 X1
       grind)
    | (have r₁ := eq1464 X0 X1
       have r₂ := eq200 X0 (k X1 X1)
       grind)
    | (have r₁ := eq1464 X0 X1
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq1464 X0 (M.op X0 X0)
       have r₂ := eq200 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1464 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq1464
  have eq1478 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1466 X0 X1 X2
       have j1 := eq283 X0 X1 X2
       grind)
    | (have r₁ := eq1466 X0 X1 X2
       have r₂ := eq283 X0 X1 (k X2 X2)
       grind)
    | (have r₁ := eq1466 X0 X1 X2
       have r₂ := eq283 X0 X1 X2
       grind)
    | (have r₁ := eq1466 X0 X1 (M.op (M.op X0 X0) X1)
       have r₂ := eq283 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq1466 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq1466
  have eq1479 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1467 X0 X1
       have j1 := eq241 X0 X1
       grind)
    | (have r₁ := eq1467 X0 X1
       have r₂ := eq241 X0 (k X1 X1)
       grind)
    | (have r₁ := eq1467 X0 X1
       have r₂ := eq241 X0 X1
       grind)
    | (have r₁ := eq1467 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)
       have r₂ := eq241 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)
       grind)
    | exact resolve eq1467 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1467
  have eq1555 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262 (M.op sF4 sF3) X1 x
       have i₂ := eq1476 (M.op sF4 sF3) X1
       grind)
    | exact superpose eq1476 eq262
    | exact resolve eq262 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1476 X0 (σ X1)
       grind)
    | exact superpose eq1476 eq10
    | exact resolve eq10 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X1 (σ X1)
       have i₂ := eq1476 X0 (σ X1)
       grind)
    | exact superpose eq1476 eq477
    | exact resolve eq477 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1566 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1476 X0 (τ X1)
       grind)
    | exact superpose eq1476 eq34
    | exact resolve eq34 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1569 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1566 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq1566
    | exact resolve eq1566 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1570 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1564 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1564
    | exact resolve eq1564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1706 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1563 X1 (M.op X0 X0)
       have i₂ := eq1298 X0
       grind)
    | exact superpose eq1298 eq1563
    | exact resolve eq1563 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1845 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1563 X1 x
       have i₂ := eq1569 X0 x
       grind)
    | exact superpose eq1569 eq1563
    | exact resolve eq1563 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1852 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1569 X0 (σ X1)
       grind)
    | exact superpose eq1569 eq10
    | exact resolve eq10 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1935 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1298 X1
       have i₂ := eq1570 X0 (M.op X1 X1)
       grind)
    | exact superpose eq1570 eq1298
    | exact resolve eq1298 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1936 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1570 X0 (σ X1)
       grind)
    | exact superpose eq1570 eq10
    | exact resolve eq10 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1937 : ∀ X0 X1 : G, (k X1 (τ (σ X1))) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X1 (σ X1)
       have i₂ := eq1570 X0 (σ X1)
       grind)
    | exact superpose eq1570 eq477
    | exact resolve eq477 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq1570
  have eq1948 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1937 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1937
    | exact resolve eq1937 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq2594 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1706 (M.op x x) X2
       have i₂ := eq251 x (M.op x x) X0 X1
       grind)
    | (have i₁ := eq1706 (M.op x x) X2
       have i₂ := eq251 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq251 eq1706
    | exact resolve eq1706 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq2615 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op x y) y) X1) = (M.op (σ (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq279 x X3 X1
       have i₂ := eq1706 X0 x
       grind)
    | exact superpose eq1706 eq279
    | exact resolve eq279 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq2616 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) = (M.op (σ (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq280 x X3 X1
       have i₂ := eq1706 X0 x
       grind)
    | exact superpose eq1706 eq280
    | exact resolve eq280 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2642 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq280 X0 X1 (M.op sF4 sF3)
       have i₂ := eq1706 X0 (M.op sF4 sF3)
       grind)
    | exact superpose eq1706 eq280
    | exact resolve eq280 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq2643 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262 (M.op sF4 sF3) X1 x
       have i₂ := eq1706 X0 (M.op sF4 sF3)
       grind)
    | exact superpose eq1706 eq262
    | exact resolve eq262 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq2842 : ∀ X0 X2 X3 : G, (k X3 X3) = (M.op (k X0 X0) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1478 (M.op x x) X2 X3
       have i₂ := eq1478 x (M.op x x) X0
       grind)
    | exact superpose eq1478 eq1478
    | exact resolve eq1478 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3239 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (k X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1706 x X2
       have i₂ := eq1555 X0 x X1
       grind)
    | (have i₁ := eq1706 (k X0 X0) X1
       have i₂ := eq1555 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq1555 eq1706
    | exact resolve eq1706 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq3241 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (τ (M.op (k X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1935 x X2
       have i₂ := eq1555 X0 x X1
       grind)
    | (have i₁ := eq1935 (k X0 X0) X1
       have i₂ := eq1555 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq1555 eq1935
    | exact resolve eq1935 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4139 : ∀ X0 X2 : G, (σ (σ (M.op X0 X0))) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1935 X2 x
       have i₂ := eq1845 X0 x
       grind)
    | exact superpose eq1845 eq1935
    | exact resolve eq1935 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4211 : ∀ X0 X2 : G, (σ (k X2 X2)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq1852 x X2
       have i₂ := eq1845 X0 x
       grind)
    | exact superpose eq1845 eq1852
    | exact resolve eq1852 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845 eq1852
  have eq4777 : ∀ X0 X1 X3 : G, (σ (k X3 X3)) = (τ (M.op (k X0 X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1936 x X3
       have i₂ := eq1555 X0 x X1
       grind)
    | (have i₁ := eq1936 (k X0 X0) X1
       have i₂ := eq1555 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq1555 eq1936
    | exact resolve eq1936 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq4783 : ∀ X0 X2 : G, (σ (k X2 X2)) = (τ (τ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq1936 x X2
       have i₂ := eq1935 X0 x
       grind)
    | exact superpose eq1935 eq1936
    | exact resolve eq1936 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq5014 : ∀ X0 X1 X3 : G, (k X1 X1) = (M.op (τ (τ (M.op X0 X0))) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2842 x X3 X1
       have i₂ := eq1948 X0 x
       grind)
    | exact superpose eq1948 eq2842
    | exact resolve eq2842 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq2842
  have eq8649 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (σ (M.op (τ (M.op X0 X0)) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2594 x X3 X1
       have i₂ := eq1935 X0 x
       grind)
    | exact superpose eq1935 eq2594
    | exact resolve eq2594 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq8896 : ∀ X0 X2 X3 : G, (σ (M.op X3 X3)) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2642 X3 x X2
       have i₂ := eq1935 X0 x
       grind)
    | exact superpose eq1935 eq2642
    | exact resolve eq2642 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642
  have eq11137 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq39
    | exact resolve eq39 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11138 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11137
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11137
    | exact resolve eq11137 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11137
  have eq11140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq11138
    | exact resolve eq11138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11138
  have eq180638 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (M.op (k X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1478 (M.op X1 X1) X2 X3
       have i₂ := eq296 X1 X0
       grind)
    | exact superpose eq296 eq1478
    | exact resolve eq1478 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq1478
  have eq252115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11140 eq1385
    | exact resolve eq1385 eq11140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11140
  have eq252127 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq252115
       have r₂ := eq27
       grind)
    | exact resolve eq252115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252115
  have eq252140 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq252127 eq181
    | exact resolve eq181 eq252127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252190 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq252127 eq1935
    | exact resolve eq1935 eq252127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935 eq252127
  have eq252437 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq252190
    | exact resolve eq252190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252190
  have eq252517 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq252140 eq252437
    | (have j0 := eq252437 y
       grind)
    | exact resolve eq252437 eq252140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252140 eq252437
  have eq252662 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 y
       have i₂ := eq252517
       grind)
    | exact superpose eq252517 eq181
    | exact resolve eq181 eq252517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252678 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1476 y X0
       have i₂ := eq252517
       grind)
    | exact superpose eq252517 eq1476
    | exact resolve eq1476 eq252517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252752 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4139 y X0
       have i₂ := eq252517
       grind)
    | exact superpose eq252517 eq4139
    | exact resolve eq4139 eq252517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq252755 : ∀ X0 : G, (σ (k X0 X0)) = (σ (σ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4211 y X0
       have i₂ := eq252517
       grind)
    | exact superpose eq252517 eq4211
    | exact resolve eq4211 eq252517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211 eq252517
  have eq252932 : ∀ X0 : G, (σ (k X0 X0)) = (σ (σ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq252755 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq252755
    | (have j0 := eq252755 X0
       grind)
    | exact resolve eq252755 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252755
  have eq252935 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq252752 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq252752
    | (have j0 := eq252752 X0
       grind)
    | exact resolve eq252752 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252752
  have eq253031 : (σ x) = (σ (σ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq252678 eq252932
    | exact resolve eq252932 eq252678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252678 eq252932
  have eq253034 : (τ x) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq252662 eq252935
    | exact resolve eq252935 eq252662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252662 eq252935
  have eq253099 : (σ x) = (σ (σ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253031
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq253031
    | exact resolve eq253031 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253031
  have eq253137 : (σ x) = (σ (τ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq253034 eq253099
    | exact resolve eq253099 eq253034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253034 eq253099
  have eq253160 : x = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253137
       have i₂ := eq14 x
       grind)
    | exact superpose eq14 eq253137
    | exact resolve eq253137 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253137
  have eq253161 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq253160
  have eq253183 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq253161 eq1479
    | exact resolve eq1479 eq253161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq253257 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq253183
    | (have j0 := eq253183 X0 X1
       grind)
    | exact resolve eq253183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253183
  have eq253303 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ x) X1) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq253161 eq253257
    | exact resolve eq253257 eq253161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253257
  have eq254175 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq253303 eq26
    | (have j1 := eq253303 X0 (σ y)
       grind)
    | exact resolve eq26 eq253303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253303
  have eq254448 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq253161 eq254175
    | exact resolve eq254175 eq253161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253161 eq254175
  have eq255876 : (τ (σ x)) = (k y y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq254448 sF3
       grind)
    | exact superpose eq254448 eq115
    | exact resolve eq115 eq254448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq255897 : x = (k y y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq255876
    | exact resolve eq255876 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq255876
  have eq256264 : x = (σ x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq254448 eq255897
    | exact resolve eq255897 eq254448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254448 eq255897
  have eq256265 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq256264
  have eq256571 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq256265
       grind)
    | exact superpose eq256265 eq18
    | exact resolve eq18 eq256265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256574 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq256265
       grind)
    | exact superpose eq256265 eq39
    | exact resolve eq39 eq256265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq256576 : (M.op x y) = (k y (σ x)) ∨ (σ x) = (M.op y y) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1384
       have i₂ := eq256265
       grind)
    | exact superpose eq256265 eq1384
    | exact resolve eq1384 eq256265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq256595 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq256265
  have eq256596 : (σ x) = (M.op y y) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq256576
       have r₂ := eq256595
       grind)
    | exact resolve eq256576 eq256595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256576
  have eq266363 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq180 y X0 X1
       have i₂ := eq256596
       grind)
    | exact superpose eq256596 eq180
    | exact resolve eq180 eq256596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266365 : ∀ X0 : G, (M.op x y) = (k y (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 y
       have i₂ := eq256596
       grind)
    | exact superpose eq256596 eq181
    | exact resolve eq181 eq256596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256596
  have eq266719 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq266365 eq266363
    | exact resolve eq266363 eq266365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266363 eq266365
  have eq268287 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq266719 eq256571
    | exact resolve eq256571 eq266719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256571 eq266719
  have eq268522 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (k y (σ x)) := by grind
  clear eq268287
  have eq268633 : (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq268522
       have r₂ := eq256595
       grind)
    | exact resolve eq268522 eq256595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268522
  have eq268726 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq268633 eq256574
    | exact resolve eq256574 eq268633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256574 eq268633
  have eq268733 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq268726
  have eq268740 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268733
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq268733
    | exact resolve eq268733 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268733
  have eq268742 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq268740
    | exact resolve eq268740 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268740
  have eq268749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq268742 eq1385
    | exact resolve eq1385 eq268742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq268772 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq268749
       have r₂ := eq27
       grind)
    | exact resolve eq268749 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268749
  have eq268858 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq268772 eq180
    | exact resolve eq180 eq268772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq268860 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq268772 eq181
    | exact resolve eq181 eq268772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268772
  have eq269216 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq268860 eq268858
    | exact resolve eq268858 eq268860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268858 eq268860
  have eq273369 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq269216 eq26
    | (have j1 := eq269216 (σ y)
       grind)
    | exact resolve eq26 eq269216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269216
  have eq273601 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq273369
  have eq273732 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq273601 eq186
    | (have r₁ := eq186
       have r₂ := eq273601
       grind)
    | exact resolve eq186 eq273601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq273778 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq273732
  have eq273824 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq268742 eq273778
    | exact resolve eq273778 eq268742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268742 eq273778
  have eq273904 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq273824 eq181
    | exact resolve eq181 eq273824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273920 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq273824 eq1476
    | exact resolve eq1476 eq273824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq273963 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (σ (M.op x y))) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq273824 eq2616
    | exact resolve eq2616 eq273824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616
  have eq274017 : ∀ X0 : G, (σ (k X0 X0)) = (τ (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq273824 eq4783
    | exact resolve eq4783 eq273824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4783
  have eq274029 : ∀ X0 X1 : G, (k X0 X0) = (M.op (τ (τ (σ (M.op x y)))) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq273824 eq5014
    | exact resolve eq5014 eq273824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5014
  have eq274058 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ (σ (M.op x y))) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq273824 eq8649
    | exact resolve eq8649 eq273824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8649
  have eq274059 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (τ (σ (M.op x y))) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq273824 eq8896
    | exact resolve eq8896 eq273824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8896 eq273824
  have eq274169 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op x y) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28 eq274059
    | exact resolve eq274059 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274059
  have eq274170 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (M.op x y) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28 eq274058
    | exact resolve eq274058 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274058
  have eq274180 : ∀ X0 X1 : G, (k X0 X0) = (M.op (τ (M.op x y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28 eq274029
    | exact resolve eq274029 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274029
  have eq274189 : ∀ X0 : G, (σ (k X0 X0)) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq274017
    | exact resolve eq274017 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq274017
  have eq274213 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (σ (M.op x y))) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq273601 eq273963
    | exact resolve eq273963 eq273601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273963
  have eq274262 : ∀ X1 : G, (M.op (M.op x y) X1) = (σ (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq273904 eq274169
    | exact resolve eq274169 eq273904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274169
  have eq274263 : ∀ X1 : G, (σ (M.op x y)) = (σ (M.op (M.op x y) X1)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq273904 eq274170
    | exact resolve eq274170 eq273904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273904 eq274170
  have eq274269 : ∀ X1 : G, (σ (M.op x y)) = (M.op (τ (M.op x y)) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq273920 eq274180
    | exact resolve eq274180 eq273920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274180
  have eq274277 : (τ (M.op x y)) = (σ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq273920 eq274189
    | exact resolve eq274189 eq273920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273920 eq274189
  have eq274291 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (σ (M.op x y))) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq274213
    | (have j0 := eq274213 X0 X1
       grind)
    | exact resolve eq274213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274213
  have eq274322 : (σ (M.op x y)) = (σ (σ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq274262 eq274263
    | exact resolve eq274263 eq274262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274262 eq274263
  have eq274337 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ (σ (M.op x y))) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq273601 eq274291
    | exact resolve eq274291 eq273601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274291
  have eq274361 : (σ (M.op x y)) = (σ (τ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq274277 eq274322
    | exact resolve eq274322 eq274277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274322
  have eq274373 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (τ (M.op x y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq274277 eq274337
    | exact resolve eq274337 eq274277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274277 eq274337
  have eq274394 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq274361
       have i₂ := eq14 sF0
       grind)
    | exact superpose eq14 eq274361
    | exact resolve eq274361 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274361
  have eq274400 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq274269 eq274373
    | exact resolve eq274373 eq274269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274269 eq274373
  have eq274420 : ∀ X0 : G, (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq274394 eq274400
    | exact resolve eq274400 eq274394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274394 eq274400
  have eq289492 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq274420 eq26
    | (have j1 := eq274420 (σ y)
       grind)
    | exact resolve eq26 eq274420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274420
  have eq290435 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq289492 eq273601
    | exact resolve eq273601 eq289492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273601 eq289492
  have eq290436 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq290435
  have eq290440 : x = (M.op x y) := by
    first
    | (have r₁ := eq290436
       have r₂ := eq256595
       grind)
    | exact resolve eq290436 eq256595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256595 eq290436
  have eq290490 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq290440
       grind)
    | exact superpose eq290440 eq18
    | exact resolve eq18 eq290440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq290491 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq290440
       grind)
    | exact superpose eq290440 eq22
    | exact resolve eq22 eq290440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq290494 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq185
       have i₂ := eq290440
       grind)
    | exact superpose eq290440 eq185
    | (have r₁ := eq185
       have r₂ := eq290440
       grind)
    | exact resolve eq185 eq290440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq290440
  have eq290513 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq290494
  have eq290515 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq290491 eq20
    | exact resolve eq20 eq290491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290491
  have eq290611 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq290490 eq178
    | exact resolve eq178 eq290490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq290707 : ∀ X0 : G, (M.op X0 X0) = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq290513 eq181
    | exact resolve eq181 eq290513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq290765 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (σ (k y (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq290513 eq2615
    | exact resolve eq2615 eq290513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq290769 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (k y (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq290513 eq2643
    | exact resolve eq2643 eq290513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643
  have eq290987 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k (σ y) (σ (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq41 eq290769
    | exact resolve eq290769 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290769
  have eq290990 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (k (σ y) (σ (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq41 eq290765
    | exact resolve eq290765 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq290765
  have eq291047 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k (σ y) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq290515 eq290987
    | exact resolve eq290987 eq290515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290987
  have eq291050 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (k (σ y) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq290515 eq290990
    | exact resolve eq290990 eq290515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290990
  have eq291100 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k (σ y) (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq291047 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq291047
    | (have j0 := eq291047 X0 X1
       grind)
    | exact resolve eq291047 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291047
  have eq291103 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (k (σ y) (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq291050 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq291050
    | (have j0 := eq291050 X0 X1
       grind)
    | exact resolve eq291050 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq291050
  have eq291137 : ∀ X1 : G, (k y (M.op x y)) = (M.op (k (σ y) (σ x)) X1) := by
    intro X1
    first
    | (have i₁ := eq291100 x X1
       have i₂ := eq290707 x
       grind)
    | exact superpose eq290707 eq291100
    | exact resolve eq291100 eq290707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290707 eq291100
  have eq291139 : ∀ X0 X1 : G, (M.op (k (σ y) (σ x)) X1) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq290490 eq291103
    | exact resolve eq291103 eq290490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291103
  have eq291159 : ∀ X0 : G, (k y (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq291137 eq291139
    | exact resolve eq291139 eq291137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291137 eq291139
  have eq292290 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq290611 eq290490
    | exact resolve eq290490 eq290611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290490 eq290611
  have eq294927 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3239 x (k x x) X0
       have i₂ := eq292290 (k x x)
       grind)
    | exact superpose eq292290 eq3239
    | exact resolve eq3239 eq292290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq294929 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3241 x (k x x) X0
       have i₂ := eq292290 (k x x)
       grind)
    | exact superpose eq292290 eq3241
    | exact resolve eq3241 eq292290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241
  have eq294940 : ∀ X0 : G, (σ (k X0 X0)) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq4777 x (k x x) X0
       have i₂ := eq292290 (k x x)
       grind)
    | exact superpose eq292290 eq4777
    | exact resolve eq4777 eq292290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4777
  have eq294951 : ∀ X0 : G, (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq180638 x x (k x (M.op x x)) X0
       have i₂ := eq292290 (k x (M.op x x))
       grind)
    | exact superpose eq292290 eq180638
    | exact resolve eq180638 eq292290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180638
  have eq294955 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq290513
       have i₂ := eq292290 sF0
       grind)
    | exact superpose eq292290 eq290513
    | exact resolve eq290513 eq292290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290513
  have eq294984 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq294940 x
       have i₂ := eq294951 x
       grind)
    | exact superpose eq294951 eq294940
    | exact resolve eq294940 eq294951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294940 eq294951
  have eq294994 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq294929 x
       have i₂ := eq292290 x
       grind)
    | exact superpose eq292290 eq294929
    | exact resolve eq294929 eq292290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294929
  have eq294996 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq294927
    | (have j0 := eq294927 X0
       grind)
    | exact resolve eq294927 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294927
  have eq295690 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq20 eq294984
    | exact resolve eq294984 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq294984
  have eq295700 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq290515 eq294996
    | exact resolve eq294996 eq290515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290515 eq294996
  have eq296179 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq294994 eq295690
    | exact resolve eq295690 eq294994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294994 eq295690
  have eq296189 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq295700 x
       have i₂ := eq292290 x
       grind)
    | exact superpose eq292290 eq295700
    | exact resolve eq295700 eq292290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292290 eq295700
  have eq297378 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq296189 eq26
    | exact resolve eq26 eq296189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq296189
  have eq297468 : (M.op (σ x) (σ y)) = (k y (M.op x y)) := by
    first
    | exact superpose eq291159 eq297378
    | exact resolve eq297378 eq291159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291159 eq297378
  have eq297475 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq294955 eq297468
    | exact resolve eq297468 eq294955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294955 eq297468
  have eq297487 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq297475 eq27
    | exact resolve eq27 eq297475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq297475
  have eq297573 : False := by grind
  exact eq297573

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_pyy_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  clear eq25
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq53 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X4 X5
       have i₂ := eq14 X4 X0 X1 X2
       grind)
    | (have i₁ := eq14 X0 (M.op (M.op X1 X2) X2) X3 X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X4 X5 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 X1 (M.op (M.op x x) x) X4 X5
       have i₂ := eq14 X0 x x X4
       grind)
    | (have i₁ := eq14 X0 X0 X0 x
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X1 (M.op x x) x X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq58 X1 X0
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq58 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq58 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq105 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq184 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq57 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq57 X0 X1 x
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq57 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq57 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq311 x X1 X2
       grind)
    | (have r₁ := eq311 x X1 X2
       have r₂ := eq58 x X1
       grind)
    | (have r₁ := eq311 X1 x X2
       have r₂ := eq58 x X1
       grind)
    | exact resolve eq311 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq426 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq11 X1 (τ X0)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 X1 (τ X0)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq517 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq318 X2 X1
       have i₂ := eq58 X1 X0
       grind)
    | (have i₁ := eq318 X2 X1
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq318
    | exact resolve eq318 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 X2))) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X1 (M.op X2 X2)
       have i₂ := eq517 X0 (τ X1) X2
       grind)
    | exact superpose eq517 eq35
    | exact resolve eq35 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G, (M.op X5 X5) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X3) X4) X6) X7) X8) X9) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    first
    | (have i₁ := eq53 X6 X6 X7 X5 X8 X9
       have i₂ := eq53 X0 X1 X2 X6 X3 X4
       grind)
    | (have i₁ := eq53 (M.op (M.op (M.op (M.op X0 X1) X1) X2) X4) X5 X2 X3 X4 X5
       have i₂ := eq53 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1131 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op X2 X2))) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq437 X1 (M.op X2 X2)
       have i₂ := eq517 X0 (σ X1) X2
       grind)
    | exact superpose eq517 eq437
    | exact resolve eq437 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq1234 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (σ (k X3 X3)) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (σ X3) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq89 X1 X1
       have i₂ := eq54 X0 (σ X1) x x
       grind)
    | exact superpose eq54 eq89
    | exact resolve eq89 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1239 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1 X1
       have i₂ := eq58 (σ X1) X1
       grind)
    | (have i₁ := eq89 X1 X1
       have i₂ := eq58 X0 (σ X1)
       grind)
    | exact superpose eq58 eq89
    | exact resolve eq89 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1242 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq89 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq89 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1283 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1286 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1291 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (σ (k X3 X3)) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (σ X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1234 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1294 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1283 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1283 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1283 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq7505 : ∀ X0 X3 : G, (σ (M.op X0 X0)) = (σ (M.op X3 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq775 X3 x x
       have i₂ := eq775 X0 x x
       grind)
    | exact superpose eq775 eq775
    | exact resolve eq775 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7865 : ∀ X0 X3 : G, (τ (M.op X0 X0)) = (τ (M.op X3 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1131 X3 x x
       have i₂ := eq1131 X0 x x
       grind)
    | exact superpose eq1131 eq1131
    | exact resolve eq1131 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12000 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1286 X0 (τ X1)
       grind)
    | exact superpose eq1286 eq35
    | (have j1 := eq1286 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq12001 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq1286 X0 x
       grind)
    | exact superpose eq1286 eq44
    | (have j1 := eq1286 X0 x
       grind)
    | exact resolve eq44 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq12026 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12001 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12001
    | (have j0 := eq12001 X0
       grind)
    | exact resolve eq12001 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12001
  have eq12027 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12000 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12000
    | (have j0 := eq12000 X0 X1
       grind)
    | exact resolve eq12000 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12000
  have eq12048 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12027 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12027
    | (have j0 := eq12027 X0 X1
       grind)
    | exact resolve eq12027 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12027
  have eq16676 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq12026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12026
  have eq17064 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12048 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17125 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17064 X2 (σ (M.op X1 X1))
       have i₂ := eq775 X0 (σ (M.op X1 X1)) X1
       grind)
    | exact superpose eq775 eq17064
    | (have j0 := eq17064 X2 (σ (M.op X1 X1))
       grind)
    | (have r₁ := eq17064 X0 (σ (M.op X0 X0))
       have r₂ := eq775 X0 (σ (M.op X0 X0)) X0
       grind)
    | exact resolve eq17064 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq17127 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17064 X2 (τ (M.op X1 X1))
       have i₂ := eq1131 X0 (τ (M.op X1 X1)) X1
       grind)
    | exact superpose eq1131 eq17064
    | (have j0 := eq17064 X2 (τ (M.op X1 X1))
       grind)
    | (have r₁ := eq17064 X0 (τ (M.op X0 X0))
       have r₂ := eq1131 X0 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq17064 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq17134 : ∀ X1 X2 : G, (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq17127 x X1 X2
       grind)
    | (have r₁ := eq17127 x x X2
       have r₂ := eq7865 x x
       grind)
    | (have r₁ := eq17127 x x X2
       have r₂ := eq7865 x x
       grind)
    | exact resolve eq17127 eq7865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7865 eq17127
  have eq17135 : ∀ X1 X2 : G, (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq17125 x X1 X2
       grind)
    | (have r₁ := eq17125 x x X2
       have r₂ := eq7505 x x
       grind)
    | (have r₁ := eq17125 x x X2
       have r₂ := eq7505 x x
       grind)
    | exact resolve eq17125 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17125
  have eq17596 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (τ (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq17135 X2 x
       have i₂ := eq17134 X0 x
       grind)
    | exact superpose eq17134 eq17135
    | exact resolve eq17135 eq17134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17135
  have eq19149 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1294 (M.op X0 X0) X1
       have i₂ := eq318 X0 (M.op X0 X0)
       grind)
    | exact superpose eq318 eq1294
    | (have j0 := eq1294 (M.op X0 X0) X1
       grind)
    | exact resolve eq1294 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq19207 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq19149 X0 X1
       grind)
    | (have r₁ := eq19149 X0 X1
       have r₂ := eq7505 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq19149 x X1
       have r₂ := eq7505 (M.op x x) x
       grind)
    | exact resolve eq19149 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7505 eq19149
  have eq19224 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19207 X2 X1
       have i₂ := eq58 X1 X0
       grind)
    | (have i₁ := eq19207 X2 X1
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq19207
    | exact resolve eq19207 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19207
  have eq20243 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq437 X1 (σ (M.op X2 X2))
       have i₂ := eq19224 X0 (σ X1) X2
       grind)
    | exact superpose eq19224 eq437
    | exact resolve eq437 eq19224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq19224
  have eq20247 : ∀ X0 X1 X2 : G, (k X1 (M.op X2 X2)) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20243 X0 X1 X2
       have i₂ := eq16 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq20243
    | exact resolve eq20243 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20243
  have eq56376 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq184 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq184
    | (have j0 := eq184 x
       grind)
    | exact resolve eq184 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq56408 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq56376
  have eq56411 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56408
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq56408
    | exact resolve eq56408 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq56408
  have eq56427 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq82 x (σ x) (σ x)
       grind)
    | (have r₁ := eq56411
       have r₂ := eq82 (σ x) (k (σ x) (σ x)) x
       grind)
    | (have r₁ := eq56411
       have r₂ := eq82 (σ x) (σ x) x
       grind)
    | exact resolve eq56411 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq56411
  have eq56434 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq56427 eq16676
    | (have j0 := eq16676 X0
       grind)
    | exact resolve eq16676 eq56427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16676
  have eq56436 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq56427 eq50
    | exact resolve eq50 eq56427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq56427
  have eq56444 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56436
       have i₂ := eq58 sF2 x
       grind)
    | (have i₁ := eq56436
       have i₂ := eq58 X0 sF2
       grind)
    | exact superpose eq58 eq56436
    | exact resolve eq56436 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56448 : ∀ X0 : G, (M.op X0 X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq56436
       have i₂ := eq17134 sF2 x
       grind)
    | exact superpose eq17134 eq56436
    | exact resolve eq56436 eq17134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17134
  have eq56449 : ∀ X0 : G, (k x x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56436
       have i₂ := eq17596 sF2 x
       grind)
    | exact superpose eq17596 eq56436
    | exact resolve eq56436 eq17596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17596 eq56436
  have eq56507 : ∀ X0 X1 : G, (k x x) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56448 x
       have i₂ := eq57 X0 x X1
       grind)
    | (have i₁ := eq56448 (M.op X0 X0)
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq56448
    | exact resolve eq56448 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq57308 : ∀ X0 X1 : G, (k x x) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56444 x
       have i₂ := eq20247 x X0 X1
       grind)
    | exact superpose eq20247 eq56444
    | exact resolve eq56444 eq20247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20247
  have eq59505 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X2) X3) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (M.op (M.op X1 X1) X2) X3) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1291 X1 X2 X3 (M.op X0 X0)
       have i₂ := eq318 X0 (M.op X0 X0)
       grind)
    | exact superpose eq318 eq1291
    | (have j0 := eq1291 X1 X2 X3 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq1291 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59730 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X1 X1) X2) (M.op X3 X3)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq318 X3 (M.op (M.op X1 X1) X2)
       have i₂ := eq1291 X1 X2 (M.op (M.op X1 X1) X2) X0
       grind)
    | exact superpose eq1291 eq318
    | (have j1 := eq1291 X1 X2 (M.op (M.op X1 X1) X2) X0
       grind)
    | exact resolve eq318 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq1291
  have eq60081 : ∀ X0 X1 X2 : G, (k x x) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59730 X0 X1 X2 x
       have i₂ := eq57308 (M.op (M.op X1 X1) X2) x
       grind)
    | exact superpose eq57308 eq59730
    | (have j0 := eq59730 X0 X1 X2 x
       grind)
    | exact resolve eq59730 eq57308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57308 eq59730
  have eq60220 : ∀ X0 X1 X2 X3 : G, (k x x) = (M.op (M.op (M.op X1 X1) X2) X3) ∨ (M.op (M.op (M.op X1 X1) X2) X3) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59505 X0 X1 X2 X3
       have i₂ := eq56449 (M.op X0 X0)
       grind)
    | exact superpose eq56449 eq59505
    | (have j0 := eq59505 X0 X1 X2 X3
       grind)
    | exact resolve eq59505 eq56449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59505
  have eq60389 : ∀ X0 : G, (k x x) = (σ (k X0 X0)) ∨ (σ X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq60081 X0 x x
       have i₂ := eq56448 (M.op (M.op x x) x)
       grind)
    | exact superpose eq56448 eq60081
    | (have j0 := eq60081 X0 x x
       grind)
    | exact resolve eq60081 eq56448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60081
  have eq60417 : ∀ X1 X2 X3 : G, (k x x) = (M.op (M.op (M.op X1 X1) X2) X3) ∨ (k x x) = (M.op (M.op (M.op X1 X1) X2) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq60220 x X1 X2 X3
       have i₂ := eq56449 x
       grind)
    | exact superpose eq56449 eq60220
    | (have j0 := eq60220 x X1 X2 X3
       grind)
    | exact resolve eq60220 eq56449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56449 eq60220
  have eq60418 : ∀ X1 X2 X3 : G, (k x x) = (M.op (M.op (M.op X1 X1) X2) X3) := by
    intro X1 X2 X3
    first
    | (have j0 := eq60417 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60417
  have eq69882 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) X3) X4) X5) X6) X7) X8) X9) (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) X3) X4) X5) X6) X7) X8) X9)) = X0 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    first
    | (have i₁ := eq793 X2 X3 X4 X5 X6 X1 X7 X8 X9 (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) X3) X4) X5) X6) X7) X8) X9)
       have i₂ := eq12048 (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) X3) X4) X5) X6) X7) X8) X9) X0
       grind)
    | exact superpose eq12048 eq793
    | (have j1 := eq12048 X1 X0
       grind)
    | exact resolve eq793 eq12048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq12048
  have eq70819 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (k x x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq69882 X0 X1 x x x x x x x x
       have i₂ := eq56448 (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op x x) x) x) x) x) x) x) x)
       grind)
    | exact superpose eq56448 eq69882
    | (have j0 := eq69882 X0 X1 x x x x x x x x
       grind)
    | exact resolve eq69882 eq56448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69882
  have eq75068 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k x x) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 X1
       have i₂ := eq56448 (τ X0)
       grind)
    | exact superpose eq56448 eq426
    | (have j0 := eq426 X0 X1
       grind)
    | exact resolve eq426 eq56448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq56448
  have eq75108 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ x = (k x x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq75068
    | exact resolve eq75068 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75068
  have eq75348 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq75108 X0
       have j1 := eq17064 X0 x
       grind)
    | (have r₁ := eq75108 X0
       have r₂ := eq17064 X0 x
       grind)
    | exact resolve eq75108 eq17064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17064 eq75108
  have eq75455 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq40 eq75348
    | (have j0 := eq75348 X0
       grind)
    | exact resolve eq75348 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq75348
  have eq92257 : ∀ X3 : G, (k x x) = (M.op (k x x) X3) := by
    intro X3
    first
    | (have i₁ := eq60418 x x X3
       have i₂ := eq56507 x x
       grind)
    | exact superpose eq56507 eq60418
    | exact resolve eq60418 eq56507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56507 eq60418
  have eq103554 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq56434 X0
       have i₂ := eq58 sF2 X1
       grind)
    | (have i₁ := eq56434 X0
       have i₂ := eq58 X0 sF2
       grind)
    | exact superpose eq58 eq56434
    | (have j0 := eq56434 X1
       grind)
    | exact resolve eq56434 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq56434
  have eq123307 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq70819 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70819
  have eq146370 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq75455 y
       grind)
    | exact superpose eq75455 eq105
    | (have j1 := eq75455 y
       grind)
    | exact resolve eq105 eq75455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq75455
  have eq146500 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq146370
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq146370
    | exact resolve eq146370 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146370
  have eq146551 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq146500
    | exact resolve eq146500 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146500
  have eq146583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq146551 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq146551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146551
  have eq146584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq103554 x (σ y)
       grind)
    | (have r₁ := eq146583
       have r₂ := eq103554 (σ y) x
       grind)
    | (have r₁ := eq146583
       have r₂ := eq103554 (σ x) x
       grind)
    | exact resolve eq146583 eq103554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103554 eq146583
  have eq146596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq146584
    | exact resolve eq146584 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146584
  have eq146598 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq146596
       have r₂ := eq28
       grind)
    | exact resolve eq146596 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146596
  have eq146683 : (τ (σ x)) = (k x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq146598 eq56444
    | exact resolve eq56444 eq146598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56444 eq146598
  have eq146793 : x = (k x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq146683
    | exact resolve eq146683 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq146683
  have eq146867 : x = (k x x) := by
    first
    | (have r₁ := eq146793
       have r₂ := eq123307 y
       grind)
    | exact resolve eq146793 eq123307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123307 eq146793
  have eq146934 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq92257 x
       have i₂ := eq146867
       grind)
    | exact superpose eq146867 eq92257
    | exact resolve eq92257 eq146867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92257
  have eq146958 : x = (σ x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq60389 x
       have i₂ := eq146867
       grind)
    | exact superpose eq146867 eq60389
    | exact resolve eq60389 eq146867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60389 eq146867
  have eq146966 : x = (σ x) := by grind
  clear eq146958
  have eq146976 : x = (σ x) := by
    first
    | (have i₁ := eq146966
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq146966
    | exact resolve eq146966 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146966
  have eq147027 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq146976 eq27
    | exact resolve eq27 eq146976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq149685 : x = (M.op x y) := by
    first
    | (have i₁ := eq146934 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq146934
    | (have j0 := eq146934 y
       grind)
    | exact resolve eq146934 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq150249 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq149685 eq21
    | exact resolve eq21 eq149685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq149685
  have eq150422 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq150249
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq150249
    | exact resolve eq150249 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq150249
  have eq150508 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq146976 eq150422
    | exact resolve eq150422 eq146976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146976 eq150422
  have eq150949 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq147027
       have i₂ := eq146934 sF3
       grind)
    | exact superpose eq146934 eq147027
    | exact resolve eq147027 eq146934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146934 eq147027
  have eq150950 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq150949 eq28
    | exact resolve eq28 eq150949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq150949
  have eq151001 : False := by grind
  exact eq151001

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_pyx_x_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq142 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq81 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq144 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq143 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq184 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq144 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq144
    | (have j0 := eq144 (τ X0)
       grind)
    | exact resolve eq144 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq144
  have eq186 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq184 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq184
    | (have j0 := eq184 X0
       grind)
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq189 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq186
    | (have j0 := eq186 X0
       grind)
    | exact resolve eq186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq200 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq189 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq189
    | (have j0 := eq189 (τ X0)
       grind)
    | exact resolve eq189 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq681 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq142 (τ X1) (τ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq142
    | (have j0 := eq142 (τ X1) (τ X0)
       grind)
    | exact resolve eq142 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq695 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq691
    | (have j0 := eq691 X0 X1
       grind)
    | exact resolve eq691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq698 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq695
    | (have j0 := eq695 X0 X1
       grind)
    | exact resolve eq695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq700 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq698
    | (have j0 := eq698 X0 X1
       grind)
    | exact resolve eq698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq702 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq700 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq700
    | (have j0 := eq700 X0 X1
       grind)
    | exact resolve eq700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq703 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq702 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq702
    | (have j0 := eq702 X0 X1
       grind)
    | exact resolve eq702 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq4089 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq87 X1 X0
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq87 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq87 X0 (σ X0)
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4111 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq4112 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq4114 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4089 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq4115 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114
  have eq4118 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4112 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4112
    | (have j0 := eq4112 X0
       grind)
    | exact resolve eq4112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4112
  have eq4156 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq4118 X0
       grind)
    | exact superpose eq4118 eq46
    | (have j1 := eq4118 X0
       grind)
    | exact resolve eq46 eq4118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq4118
  have eq4167 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4156 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4156
    | (have j0 := eq4156 X0
       grind)
    | exact resolve eq4156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4156
  have eq4168 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4167
  have eq4170 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4168 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4168
    | exact resolve eq4168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4193 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4168 X0
       grind)
    | exact superpose eq4168 eq11
    | exact resolve eq11 eq4168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq4253 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4170 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4170
    | exact resolve eq4170 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4170
  have eq4474 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq200 X0
       have i₂ := eq4253 X0
       grind)
    | exact superpose eq4253 eq200
    | (have j0 := eq200 X0
       grind)
    | exact resolve eq200 eq4253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq4478 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4253 X0
       grind)
    | exact superpose eq4253 eq11
    | exact resolve eq11 eq4253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4588 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4478 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4478
    | exact resolve eq4478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq4650 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq4588 (τ X0)
       grind)
    | exact superpose eq4588 eq34
    | exact resolve eq34 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4706 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4650 X0
       have i₂ := eq4253 X0
       grind)
    | exact superpose eq4253 eq4650
    | exact resolve eq4650 eq4253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253 eq4650
  have eq5242 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq5259 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5242 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq5242
    | exact resolve eq5242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5242
  have eq5288 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5259 X0
       have i₂ := eq4588 X0
       grind)
    | exact superpose eq4588 eq5259
    | exact resolve eq5259 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5259
  have eq5301 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5288
  have eq23728 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq4115 (σ X0) X1
       grind)
    | exact superpose eq4115 eq30
    | (have j1 := eq4115 (σ X0) X1
       grind)
    | exact resolve eq30 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4115
  have eq23819 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23728 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq23728
    | (have j0 := eq23728 X0 X1
       grind)
    | exact resolve eq23728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23728
  have eq23893 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23819 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23819
    | (have j0 := eq23819 X0 X1
       grind)
    | exact resolve eq23819 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23819
  have eq23960 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23893 X0 X1
       have i₂ := eq4193 X0
       grind)
    | exact superpose eq4193 eq23893
    | (have j0 := eq23893 X0 X1
       grind)
    | exact resolve eq23893 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23893
  have eq24006 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23960 X0 X1
       have i₂ := eq4588 X0
       grind)
    | exact superpose eq4588 eq23960
    | (have j0 := eq23960 X0 X1
       grind)
    | exact resolve eq23960 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23960
  have eq24045 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24006 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24006
    | (have j0 := eq24006 X0 X1
       grind)
    | exact resolve eq24006 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24006
  have eq26446 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24045 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24045
    | (have j0 := eq24045 X1 (τ X0)
       grind)
    | exact resolve eq24045 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26527 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq24045 X0 X1
       grind)
    | exact superpose eq24045 eq11
    | (have j1 := eq24045 X0 X1
       grind)
    | exact resolve eq11 eq24045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24045
  have eq27063 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26446 X0 (τ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq26446
    | (have j0 := eq26446 X1 (τ X0)
       grind)
    | exact resolve eq26446 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq26446
  have eq27248 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27063 X0 X1
       have i₂ := eq4706 X0
       grind)
    | exact superpose eq4706 eq27063
    | (have j0 := eq27063 X0 X1
       grind)
    | exact resolve eq27063 eq4706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27063
  have eq27332 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27248 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq27248
    | (have j0 := eq27248 X0 X1
       grind)
    | exact resolve eq27248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27248
  have eq27405 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27332 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27332
    | (have j0 := eq27332 X0 X1
       grind)
    | exact resolve eq27332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27332
  have eq27776 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27405
  have eq29510 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26527 y x
       grind)
    | exact superpose eq26527 eq16
    | (have j1 := eq26527 y x
       grind)
    | exact resolve eq16 eq26527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26527
  have eq30451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29510
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq29510
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq29510 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29510
  have eq30454 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq30451
  have eq30455 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq30454
  have eq30466 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27776 y x
       have i₂ := eq30455
       grind)
    | exact superpose eq30455 eq27776
    | (have j0 := eq27776 y x
       grind)
    | exact resolve eq27776 eq30455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27776 eq30455
  have eq30467 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ y) = (τ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq30466
  have eq30468 : x = (M.op y y) ∨ (τ y) = (τ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq30467
  have eq30899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq5301 y
       have i₂ := eq30468
       grind)
    | exact superpose eq30468 eq5301
    | exact resolve eq5301 eq30468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30468
  have eq30920 : (σ x) = (σ (M.op y y)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have r₁ := eq30899
       have r₂ := eq16
       grind)
    | exact resolve eq30899 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30899
  have eq31314 : (M.op y y) = (τ (σ x)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq30920
       grind)
    | exact superpose eq30920 eq10
    | exact resolve eq10 eq30920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30920
  have eq31441 : x = (M.op y y) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq31314
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31314
    | exact resolve eq31314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31314
  have eq31512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k y x)) := by
    first
    | (have i₁ := eq5301 y
       have i₂ := eq31441
       grind)
    | exact superpose eq31441 eq5301
    | exact resolve eq5301 eq31441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31441
  have eq31533 : (τ y) = (τ (k y x)) := by
    first
    | (have r₁ := eq31512
       have r₂ := eq16
       grind)
    | exact resolve eq31512 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31512
  have eq31924 : (k y x) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq31533
       grind)
    | exact superpose eq31533 eq11
    | exact resolve eq11 eq31533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31533
  have eq32095 : y = (k y x) := by
    first
    | (have i₁ := eq31924
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq31924
    | exact resolve eq31924 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31924
  have eq32162 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq142 x y
       have i₂ := eq32095
       grind)
    | exact superpose eq32095 eq142
    | (have j0 := eq142 x y
       grind)
    | exact resolve eq142 eq32095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq32167 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq703 y x
       have i₂ := eq32095
       grind)
    | exact superpose eq32095 eq703
    | (have j0 := eq703 y x
       grind)
    | (have r₁ := eq703 y x
       have r₂ := eq32095
       grind)
    | exact resolve eq703 eq32095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq32095
  have eq32170 : y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq32167
  have eq32172 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq32162
  have eq32178 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32172
       have i₂ := eq4193 y
       grind)
    | exact superpose eq4193 eq32172
    | exact resolve eq32172 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32172
  have eq32184 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq32178
       have i₂ := eq4588 y
       grind)
    | exact superpose eq4588 eq32178
    | exact resolve eq32178 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32178
  have eq32574 : y = (M.op y (M.op y (M.op y y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq32170
       grind)
    | exact superpose eq32170 eq9
    | exact resolve eq9 eq32170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35157 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq32574
       grind)
    | exact superpose eq32574 eq9
    | exact resolve eq9 eq32574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32574
  have eq35564 : (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4474 y
       have i₂ := eq35157
       grind)
    | exact superpose eq35157 eq4474
    | (have j0 := eq4474 y
       grind)
    | exact resolve eq4474 eq35157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474 eq35157
  have eq35586 : (τ y) = (M.op (τ y) (τ y)) ∨ x = (M.op y y) := by grind
  clear eq35564
  have eq35599 : x = (M.op y y) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq35586
       have i₂ := eq4706 y
       grind)
    | exact superpose eq4706 eq35586
    | exact resolve eq35586 eq4706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706 eq35586
  have eq35977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq5301 y
       have i₂ := eq35599
       grind)
    | exact superpose eq35599 eq5301
    | exact resolve eq5301 eq35599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5301 eq35599
  have eq35999 : (τ y) = (τ (M.op y y)) := by
    first
    | (have r₁ := eq35977
       have r₂ := eq16
       grind)
    | exact resolve eq35977 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35977
  have eq36023 : (M.op y y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (M.op y y)
       have i₂ := eq35999
       grind)
    | exact superpose eq35999 eq11
    | exact resolve eq11 eq35999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35999
  have eq36205 : y = (M.op y y) := by
    first
    | (have i₁ := eq36023
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq36023
    | exact resolve eq36023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36023
  have eq39170 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32184
       grind)
    | exact superpose eq32184 eq16
    | exact resolve eq16 eq32184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32184
  have eq39196 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39170
       have i₂ := eq36205
       grind)
    | exact superpose eq36205 eq39170
    | exact resolve eq39170 eq36205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39170
  have eq39697 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39196
       have i₂ := eq32170
       grind)
    | exact superpose eq32170 eq39196
    | exact resolve eq39196 eq32170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32170 eq39196
  have eq39700 : (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq39697
  have eq39703 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39700
       have i₂ := eq36205
       grind)
    | exact superpose eq36205 eq39700
    | exact resolve eq39700 eq36205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36205 eq39700
  have eq39705 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39703
       grind)
    | exact superpose eq39703 eq16
    | exact resolve eq16 eq39703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39703
  have eq39754 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39705
       have i₂ := eq4193 x
       grind)
    | exact superpose eq4193 eq39705
    | exact resolve eq39705 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39705
  have eq39759 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39754
       have i₂ := eq4588 x
       grind)
    | exact superpose eq4588 eq39754
    | exact resolve eq39754 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39754
  have eq39760 : (σ x) = (σ y) := by grind
  clear eq39759
  have eq40220 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39760
       grind)
    | exact superpose eq39760 eq16
    | exact resolve eq16 eq39760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40221 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq39760
       grind)
    | exact superpose eq39760 eq10
    | exact resolve eq10 eq39760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39760
  have eq40367 : x = y := by
    first
    | (have i₁ := eq40221
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40221
    | exact resolve eq40221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40221
  have eq40368 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq40220
       have i₂ := eq4193 x
       grind)
    | exact superpose eq4193 eq40220
    | exact resolve eq40220 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193 eq40220
  have eq40417 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq40368
       have i₂ := eq4588 x
       grind)
    | exact superpose eq4588 eq40368
    | exact resolve eq40368 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4588 eq40368
  have eq40464 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq40417
       have i₂ := eq40367
       grind)
    | exact superpose eq40367 eq40417
    | exact resolve eq40417 eq40367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40367 eq40417
  have eq40465 : False := by grind
  exact eq40465

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq77 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq9
    | exact resolve eq9 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq15
    | (have j1 := eq92 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq92 (τ X0) X1
       grind)
    | exact superpose eq92 eq17
    | (have j1 := eq92 (τ X0) X1
       grind)
    | exact resolve eq17 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq534 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq126 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126
    | exact resolve eq126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq577 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq534
    | (have j0 := eq534 X0 X1
       grind)
    | exact resolve eq534 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq886 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq124 x y
       grind)
    | exact superpose eq124 eq16
    | (have j1 := eq124 x y
       grind)
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq903 (τ X0) (τ X1)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq903
    | (have j0 := eq903 (τ X0) (τ X1)
       grind)
    | exact resolve eq903 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq903
  have eq932 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq924 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq924
    | (have j0 := eq924 X0 X1
       grind)
    | exact resolve eq924 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq935 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq932 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq932
    | (have j0 := eq932 X0 X1
       grind)
    | exact resolve eq932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq936 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq935 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq935
    | (have j0 := eq935 X0 X1
       grind)
    | exact resolve eq935 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq937 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq936 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq936
    | (have j0 := eq936 X0 X1
       grind)
    | exact resolve eq936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq886
       have i₂ := eq577 x y
       grind)
    | exact superpose eq577 eq886
    | (have j1 := eq577 (σ x) (σ y)
       grind)
    | (have r₁ := eq886
       have r₂ := eq577 x y
       grind)
    | exact resolve eq886 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq1163 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1162
  have eq1167 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq9
    | exact resolve eq9 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1205 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq1167
       grind)
    | exact superpose eq1167 eq9
    | exact resolve eq9 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1219 : y = (M.op y (M.op y (M.op y y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq1205
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq1205
    | exact resolve eq1205 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq27283 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq1219
       grind)
    | exact superpose eq1219 eq9
    | exact resolve eq9 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq27656 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq27283
       grind)
    | exact superpose eq27283 eq77
    | exact resolve eq77 eq27283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27283
  have eq27683 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
    first
    | (have i₁ := eq27656
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq27656
    | exact resolve eq27656 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27656
  have eq27684 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by grind
  clear eq27683
  have eq27714 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq27684
       grind)
    | exact superpose eq27684 eq77
    | exact resolve eq77 eq27684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq27684
  have eq27761 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq27714
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq27714
    | exact resolve eq27714 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27714
  have eq28245 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq27761
       grind)
    | exact superpose eq27761 eq10
    | exact resolve eq10 eq27761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28247 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (M.op y y)
       have i₂ := eq27761
       grind)
    | exact superpose eq27761 eq15
    | exact resolve eq15 eq27761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28265 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq124 X0 (M.op y y)
       have i₂ := eq27761
       grind)
    | exact superpose eq27761 eq124
    | (have j0 := eq124 X0 y
       grind)
    | exact resolve eq124 eq27761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq28340 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq28247 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq28247
    | exact resolve eq28247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28247
  have eq28342 : y = (M.op y y) := by
    first
    | (have i₁ := eq28245
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq28245
    | exact resolve eq28245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28245
  have eq37680 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x (M.op y y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28265 x
       grind)
    | exact superpose eq28265 eq16
    | (have j1 := eq28265 x
       grind)
    | exact resolve eq16 eq28265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37699 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ X0)) ∨ (σ y) = (k (σ X0) (σ y)) ∨ (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ y)
       have i₂ := eq28265 X0
       grind)
    | exact superpose eq28265 eq12
    | (have j1 := eq28265 X0
       grind)
    | exact resolve eq12 eq28265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37700 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ X0) (σ y)
       have i₂ := eq28265 X0
       grind)
    | exact superpose eq28265 eq13
    | (have j0 := eq13 (σ X0) (σ y)
       have j1 := eq28265 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ y)
       have r₂ := eq28265 X0
       grind)
    | exact resolve eq13 eq28265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28265
  have eq37714 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37700
  have eq37725 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k X0 y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37714 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq37714
    | (have j0 := eq37714 X0
       grind)
    | exact resolve eq37714 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37714
  have eq37726 : ∀ X0 : G, (σ y) = (σ (k X0 y)) ∨ (σ y) ≠ (M.op (σ y) (σ X0)) ∨ (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37699 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq37699
    | (have j0 := eq37699 X0
       grind)
    | exact resolve eq37699 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37699
  have eq37743 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq37680
       have i₂ := eq28340 x
       grind)
    | exact superpose eq28340 eq37680
    | exact resolve eq37680 eq28340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37680
  have eq37794 : ∀ X0 : G, (σ (M.op y y)) = (σ (k X0 y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37725 X0
       have i₂ := eq39 y
       grind)
    | exact superpose eq39 eq37725
    | (have j0 := eq37725 X0
       grind)
    | exact resolve eq37725 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq37725
  have eq37795 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k X0 y)) ∨ (σ y) ≠ (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37726 X0
       have i₂ := eq28340 X0
       grind)
    | exact superpose eq28340 eq37726
    | (have j0 := eq37726 X0
       grind)
    | exact resolve eq37726 eq28340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37726
  have eq37826 : ∀ X0 : G, (σ y) = (σ (k X0 y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ (k X0 (M.op y y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37794 X0
       have i₂ := eq27761
       grind)
    | exact superpose eq27761 eq37794
    | (have j0 := eq37794 X0
       grind)
    | exact resolve eq37794 eq27761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27761 eq37794
  have eq37842 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k X0 y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37826 X0
       have i₂ := eq28340 X0
       grind)
    | exact superpose eq28340 eq37826
    | (have j0 := eq37826 X0
       grind)
    | exact resolve eq37826 eq28340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28340 eq37826
  have eq37857 : ∀ X0 : G, (σ y) = (σ (k X0 y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37842 X0
       have j1 := eq37795 X0
       grind)
    | (have r₁ := eq37842 X0
       have r₂ := eq37795 X0
       grind)
    | exact resolve eq37842 eq37795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37795 eq37842
  have eq38264 : ∀ X0 : G, (τ (σ y)) = (k X0 y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 y)
       have i₂ := eq37857 X0
       grind)
    | exact superpose eq37857 eq10
    | (have j1 := eq37857 X0
       grind)
    | exact resolve eq10 eq37857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37857
  have eq38376 : ∀ X0 : G, y = (k X0 y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq38264 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq38264
    | (have j0 := eq38264 X0
       grind)
    | exact resolve eq38264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38264
  have eq38444 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq937 X0 y
       have i₂ := eq38376 X0
       grind)
    | exact superpose eq38376 eq937
    | (have j0 := eq937 X0 y
       have j1 := eq38376 X0
       grind)
    | (have r₁ := eq937 X0 y
       have r₂ := eq38376 X0
       grind)
    | exact resolve eq937 eq38376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq38376
  have eq38567 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq38444 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38444
  have eq39093 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq37743
       have i₂ := eq38567 x
       grind)
    | exact superpose eq38567 eq37743
    | (have j1 := eq38567 x
       grind)
    | exact resolve eq37743 eq38567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37743 eq38567
  have eq39100 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq39093
  have eq39101 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq39100
  have eq39273 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39101
       grind)
    | exact superpose eq39101 eq16
    | exact resolve eq16 eq39101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39101
  have eq39894 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39273
       have i₂ := eq577 x y
       grind)
    | exact superpose eq577 eq39273
    | (have j1 := eq577 x y
       grind)
    | (have r₁ := eq39273
       have r₂ := eq577 x y
       grind)
    | exact resolve eq39273 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq39895 : y = (M.op x y) := by grind
  clear eq39894
  have eq39909 : y ≠ y ∨ (k x y) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq39895
       grind)
    | exact superpose eq39895 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq39895
       grind)
    | exact resolve eq13 eq39895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39921 : (k x y) = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq39909
  have eq39940 : y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39921
       have i₂ := eq28342
       grind)
    | exact superpose eq28342 eq39921
    | exact resolve eq39921 eq28342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28342 eq39921
  have eq40277 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq39940
       grind)
    | exact superpose eq39940 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq39940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39940
  have eq40323 : (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have j1 := eq92 x y
       grind)
    | (have r₁ := eq40277
       have r₂ := eq92 x y
       grind)
    | exact resolve eq40277 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq40277
  have eq40337 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq40323
       have i₂ := eq39895
       grind)
    | exact superpose eq39895 eq40323
    | exact resolve eq40323 eq39895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40323
  have eq40338 : y = (k x y) := by grind
  clear eq40337
  have eq40349 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq39273
       have i₂ := eq40338
       grind)
    | exact superpose eq40338 eq39273
    | exact resolve eq39273 eq40338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39273 eq40338
  have eq40427 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq40349
       have i₂ := eq39895
       grind)
    | exact superpose eq39895 eq40349
    | exact resolve eq40349 eq39895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39895 eq40349
  have eq40428 : False := by grind
  exact eq40428

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pyx_pyx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq396 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2985 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq396 X0 X1
       grind)
    | (have i₁ := eq12 X0 (σ X1)
       have i₂ := eq396 X0 X1
       grind)
    | exact superpose eq396 eq12
    | (have j1 := eq396 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) X0
       have r₂ := eq396 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq396 X0 X1
       grind)
    | exact resolve eq12 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq2987 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2985 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985
  have eq3864 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq2987 X0 X1
       grind)
    | exact superpose eq2987 eq23
    | (have j1 := eq2987 X0 X1
       grind)
    | exact resolve eq23 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2987
  have eq3899 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3864 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3864
  have eq3912 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3899 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3899
    | exact resolve eq3899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3899
  have eq4009 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3912 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq3912
    | (have j0 := eq3912 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq3912 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3912
  have eq4041 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4009 X1 X0
       grind)
    | exact superpose eq4009 eq11
    | (have j1 := eq4009 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq4009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4009
  have eq4158 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4041 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4041
    | (have j0 := eq4041 (M.op X0 X1) (k X0 X1)
       grind)
    | exact resolve eq4041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4041
  have eq4204 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq4158 X0 (τ X1)
       grind)
    | exact superpose eq4158 eq19
    | (have j1 := eq4158 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq4158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq4226 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4158 (σ X0) (σ X1)
       grind)
    | exact superpose eq4158 eq15
    | (have j1 := eq4158 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq4158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4158
  have eq4462 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4204 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4204
    | exact resolve eq4204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4524 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4462 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4462
    | (have j0 := eq4462 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq4462 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4462
  have eq4895 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4226 x y
       grind)
    | exact superpose eq4226 eq16
    | (have j1 := eq4226 x y
       grind)
    | exact resolve eq16 eq4226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4895
       have i₂ := eq4524 y x
       grind)
    | exact superpose eq4524 eq4895
    | (have j1 := eq4524 (σ x) (σ y)
       grind)
    | (have r₁ := eq4895
       have r₂ := eq4524 y x
       grind)
    | (have r₁ := eq4895
       have r₂ := eq4524 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4895
       have r₂ := eq4524 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4895 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4524 eq4895
  have eq4934 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq4931
  have eq4937 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4934
       grind)
    | exact superpose eq4934 eq16
    | exact resolve eq16 eq4934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4934
  have eq4938 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq4937
       have r₂ := eq77 x
       grind)
    | exact resolve eq4937 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937
  have eq4939 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq16
    | exact resolve eq16 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4940 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4938
       grind)
    | exact superpose eq4938 eq10
    | exact resolve eq10 eq4938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4938
  have eq4993 : x = y := by
    first
    | (have i₁ := eq4940
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4940
    | exact resolve eq4940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4940
  have eq4994 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4939
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq4939
    | exact resolve eq4939 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq4939
  have eq4995 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4994
       have i₂ := eq4993
       grind)
    | exact superpose eq4993 eq4994
    | exact resolve eq4994 eq4993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4993 eq4994
  have eq4996 : False := by grind
  exact eq4996
