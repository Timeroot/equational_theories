import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation655`: `x = x ◇ (y ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxy_pxx_pxy_Equation655 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law655 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law655.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X1) X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X2) X3)) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X2 (M.op (M.op X3 X2) X3)) X0
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 (M.op X0 (M.op (M.op X1 X0) X1))
       have i₂ := eq9 (M.op (M.op X0 (M.op (M.op X1 X0) X1)) X2) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq31 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27
    | exact resolve eq27 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq31
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 x x (M.op X0 X0) X1
       have i₂ := eq24 X0 (M.op X0 X0) x x
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq118 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq94
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op (M.op X1 X0) X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 (M.op X0 (M.op (M.op X1 X0) X1)) X2
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 X0) X1)) X0 X1
       grind)
    | exact superpose eq9 eq118
    | exact resolve eq118 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq227 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 x y
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq286 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq10
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq479 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq94 (τ X0) X1
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq94
    | exact resolve eq94 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq556 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op (M.op X1 X0) X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq479 (M.op X0 (M.op (M.op X1 X0) X1)) X2
       have i₂ := eq9 (M.op X0 (M.op (M.op X1 X0) X1)) X0 X1
       grind)
    | exact superpose eq9 eq479
    | exact resolve eq479 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq6743 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq227
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq227
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq227
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq227
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq227 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq6744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq6743
  have eq69812 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (M.op (σ x) (σ x))))) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq556 (σ y) (σ x) X0
       have i₂ := eq6744
       grind)
    | exact superpose eq6744 eq556
    | exact resolve eq556 eq6744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq6744
  have eq69826 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq69812 X0
       have i₂ := eq94 (σ x) (σ y)
       grind)
    | exact superpose eq94 eq69812
    | exact resolve eq69812 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69812
  have eq69866 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq69826 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq69826
    | exact resolve eq69826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69826
  have eq451338 : x ≠ x ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq69866 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69866
  have eq451339 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq451338
  have eq452253 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq451339
       grind)
    | exact superpose eq451339 eq9
    | exact resolve eq9 eq451339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452258 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op x x)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq188 y x X0
       have i₂ := eq451339
       grind)
    | exact superpose eq451339 eq188
    | exact resolve eq188 eq451339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq451339
  have eq452323 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq452258 X0
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq452258
    | exact resolve eq452258 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452258
  have eq452327 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq452253 X0
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq452253
    | exact resolve eq452253 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq452253
  have eq458055 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq452323 (σ x)
       grind)
    | exact superpose eq452323 eq16
    | exact resolve eq16 eq452323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452323
  have eq465731 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq458055
       have i₂ := eq452327 x
       grind)
    | exact superpose eq452327 eq458055
    | exact resolve eq458055 eq452327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452327 eq458055
  have eq465732 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq465731
  have eq465733 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq465732
  have eq467044 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq465733
       grind)
    | exact superpose eq465733 eq10
    | exact resolve eq10 eq465733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465733
  have eq467101 : x = y ∨ x = y := by
    first
    | (have i₁ := eq467044
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq467044
    | exact resolve eq467044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467044
  have eq467102 : x = y := by grind
  clear eq467101
  have eq468459 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq467102
       grind)
    | exact superpose eq467102 eq16
    | exact resolve eq16 eq467102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467102
  have eq468460 : False := by grind
  exact eq468460

/-- `Equation679`: `x = y ◇ (x ◇ ((y ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation679 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law679 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law679.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq299 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq326 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq299 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq299
    | (have j0 := eq299 X0 X1
       grind)
    | exact resolve eq299 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq782 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq72
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq72
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq72
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq783 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq782
  have eq4815 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq783
       grind)
    | exact superpose eq783 eq16
    | exact resolve eq16 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4816 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq783
       grind)
    | exact superpose eq783 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq783
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq783
       grind)
    | exact resolve eq13 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq4817 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4816
  have eq4818 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4817
  have eq4820 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4818
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4818
    | exact resolve eq4818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4818
  have eq7168 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq326 y x
       have i₂ := eq4820
       grind)
    | exact superpose eq4820 eq326
    | (have j0 := eq326 y x
       grind)
    | exact resolve eq326 eq4820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq7170 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq4820
       grind)
    | exact superpose eq4820 eq10
    | exact resolve eq10 eq4820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4820
  have eq7212 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7168
  have eq7239 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7170
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7170
    | exact resolve eq7170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170
  have eq7240 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7212
       have r₂ := eq4815
       grind)
    | exact resolve eq7212 eq4815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4815 eq7212
  have eq7243 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq7239
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7239 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7239
  have eq7629 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq74 x y
       have i₂ := eq7243
       grind)
    | exact superpose eq7243 eq74
    | (have j0 := eq74 x y
       grind)
    | exact resolve eq74 eq7243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq7243
  have eq7632 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7629
  have eq7633 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7632
  have eq7803 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq7633
       grind)
    | exact superpose eq7633 eq16
    | exact resolve eq16 eq7633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7633
  have eq7966 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7803
       have i₂ := eq7240
       grind)
    | exact superpose eq7240 eq7803
    | exact resolve eq7803 eq7240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7240 eq7803
  have eq7967 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7966
  have eq7968 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq7967
  have eq8171 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq7968
       grind)
    | exact superpose eq7968 eq10
    | exact resolve eq10 eq7968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7968
  have eq8248 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8171
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8171
    | exact resolve eq8171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171
  have eq8249 : x = y := by grind
  clear eq8248
  have eq8466 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8249
       grind)
    | exact superpose eq8249 eq16
    | exact resolve eq16 eq8249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8249
  have eq8467 : False := by grind
  exact eq8467

/-- `Equation703`: `x = y ◇ (y ◇ ((x ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation703 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law703 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law703.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq74 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq290 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq321 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq290
    | (have j0 := eq290 X0 X1
       grind)
    | exact resolve eq290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq686 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq74
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq74
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq74
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq74 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq687 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq686
  have eq3989 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq16
    | exact resolve eq16 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3990 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq687
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq687
       grind)
    | exact resolve eq13 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq3991 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3990
  have eq3992 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3991
  have eq3994 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3992
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3992
    | exact resolve eq3992 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq76521 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq321 x y
       have i₂ := eq3994
       grind)
    | exact superpose eq3994 eq321
    | (have j0 := eq321 x y
       grind)
    | exact resolve eq321 eq3994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq76523 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq3994
       grind)
    | exact superpose eq3994 eq10
    | exact resolve eq10 eq3994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3994
  have eq76631 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq76521
  have eq76670 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq76523
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq76523
    | exact resolve eq76523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76523
  have eq76671 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq76631
       have r₂ := eq3989
       grind)
    | exact resolve eq76631 eq3989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989 eq76631
  have eq76676 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq76670
       have r₂ := eq13 y x
       grind)
    | exact resolve eq76670 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76670
  have eq77574 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq76 x y
       have i₂ := eq76676
       grind)
    | exact superpose eq76676 eq76
    | (have j0 := eq76 x y
       grind)
    | exact resolve eq76 eq76676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq76676
  have eq77577 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq77574
  have eq77578 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq77577
  have eq77911 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq77578
       grind)
    | exact superpose eq77578 eq16
    | exact resolve eq16 eq77578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77578
  have eq78360 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq77911
       have i₂ := eq76671
       grind)
    | exact superpose eq76671 eq77911
    | exact resolve eq77911 eq76671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76671 eq77911
  have eq78361 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq78360
  have eq78362 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq78361
  have eq78782 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq78362
       grind)
    | exact superpose eq78362 eq10
    | exact resolve eq10 eq78362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78362
  have eq78936 : x = y ∨ x = y := by
    first
    | (have i₁ := eq78782
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq78782
    | exact resolve eq78782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78782
  have eq78937 : x = y := by grind
  clear eq78936
  have eq79360 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78937
       grind)
    | exact superpose eq78937 eq16
    | exact resolve eq16 eq78937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78937
  have eq79361 : False := by grind
  exact eq79361

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation727 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law727 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (σ X0) X2)) = (M.op (σ (M.op X0 X0)) (M.op (M.op X1 (σ (M.op X0 X0))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 (σ X0) (σ X0) x
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X1) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 (M.op X2 X0)) X1) X0 X2
       have i₂ := eq26 X1 X0 X2 X3
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) x
       have i₂ := eq26 X1 X0 X2 x
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq270 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq347 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq116
    | exact resolve eq116 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) X0)) = (M.op (M.op X1 X2) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq116 X2 (M.op X2 (M.op (M.op X3 X2) X0)) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq116
    | exact resolve eq116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq116 X2 (M.op (M.op X3 X2) X0) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq116
    | exact resolve eq116 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq359 X3 X1 (M.op X2 (M.op X2 X0)) (M.op x X2)
       have i₂ := eq116 X2 X0 x
       grind)
    | exact superpose eq116 eq359
    | exact resolve eq359 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359 X2 X1 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq359
    | exact resolve eq359 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1514 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq347 X0 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq347
    | exact resolve eq347 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1516 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0)) = (M.op (σ (M.op X1 X1)) (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq347 X1 (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0))
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq347
    | exact resolve eq347 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1544 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ X1) (M.op (σ X1) X0)) X2) = (M.op (M.op X3 (M.op (σ (M.op X1 X1)) X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq438 (M.op (σ X1) (M.op (σ X1) X0)) X3 (σ (M.op X1 X1)) X2
       have i₂ := eq347 X1 X0
       grind)
    | exact superpose eq347 eq438
    | exact resolve eq438 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq438
  have eq1554 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1514 X0
       have i₂ := eq1516 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq1516 eq1514
    | exact resolve eq1514 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514 eq1516
  have eq1564 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1554 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq1554
    | exact resolve eq1554 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq1777 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X4 X3) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq115 X3 (M.op (M.op X4 X3) X0) X2 X1
       have i₂ := eq9 X0 X3 X4
       grind)
    | exact superpose eq9 eq115
    | exact resolve eq115 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq3001 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1564 X1
       have i₂ := eq359 (M.op X1 X1) X1 X1 X0
       grind)
    | (have i₁ := eq1564 X1
       have i₂ := eq359 (M.op X1 X1) X0 X1 X1
       grind)
    | exact superpose eq359 eq1564
    | exact resolve eq1564 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq1564
  have eq6679 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq270
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq270
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq270
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq270
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq6681 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq6679
  have eq7203 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3001 x X0
       have i₂ := eq350 X0 x X0 X1
       grind)
    | exact superpose eq350 eq3001
    | exact resolve eq3001 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq61037 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X0) X0)) = (M.op (σ (M.op (M.op X1 X0) X0)) (σ (M.op (M.op (M.op X1 X0) X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7203 (M.op (M.op X1 X0) X0) x
       have i₂ := eq1777 X0 x (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq1777 eq7203
    | exact resolve eq7203 eq1777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7203
  have eq61376 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X0) X0)) = (M.op (σ (M.op (M.op X1 X0) X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61037 X0 X1
       have i₂ := eq116 X0 X0 (M.op X1 X0)
       grind)
    | exact superpose eq116 eq61037
    | exact resolve eq61037 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq61037
  have eq62882 : ∀ X0 X1 : G, (σ (M.op (M.op X1 (τ X0)) (τ X0))) = (M.op (σ (M.op (M.op X1 (τ X0)) (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61376 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61376
    | exact resolve eq61376 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62905 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 X1)) X2) = (M.op (σ (M.op (M.op X0 X1) X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 X1 (σ (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq61376 X1 X0
       grind)
    | exact superpose eq61376 eq441
    | exact resolve eq441 eq61376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61376
  have eq63062 : ∀ X0 X1 : G, (σ (M.op (M.op X1 (τ X0)) (τ X0))) = (M.op (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62882 X0 X1
       have i₂ := eq62905 X1 (τ X0) X0
       grind)
    | exact superpose eq62905 eq62882
    | exact resolve eq62882 eq62905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62882 eq62905
  have eq63155 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (M.op X1 (τ X0)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63062 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq63062
    | exact resolve eq63062 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq63062
  have eq63933 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X1)) = (σ (M.op (M.op X0 (τ (σ X1))) (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X1 (σ X1) (σ X1)
       have i₂ := eq63155 (σ X1) X0
       grind)
    | exact superpose eq63155 eq441
    | exact resolve eq441 eq63155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63155
  have eq64327 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X1)) = (σ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63933 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63933
    | exact resolve eq63933 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63933
  have eq80489 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X1)) = (σ (M.op (M.op X2 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64327 X2 X1
       have i₂ := eq64327 X0 X1
       grind)
    | exact superpose eq64327 eq64327
    | exact resolve eq64327 eq64327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80676 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X1 X1)) (M.op (M.op X2 (σ (M.op X1 X1))) (σ X1))) = (M.op (M.op X3 (σ (M.op X1 X1))) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq350 (σ X1) X3 (σ (M.op X1 X1)) X2
       have i₂ := eq64327 X0 X1
       grind)
    | exact superpose eq64327 eq350
    | exact resolve eq350 eq64327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq80775 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0))) X3) = (M.op (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq441 (M.op (M.op X2 X0) X0) X1 X3
       have i₂ := eq64327 X2 X0
       grind)
    | exact superpose eq64327 eq441
    | exact resolve eq441 eq64327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq80802 : ∀ X0 X2 X3 : G, (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) X3) = (M.op (σ (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq80775 X0 x X2 X3
       have i₂ := eq1544 (σ X0) X0 X3 x
       grind)
    | exact superpose eq1544 eq80775
    | exact resolve eq80775 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544 eq80775
  have eq80842 : ∀ X0 X1 X3 : G, (M.op (σ X1) (M.op (σ X1) (σ X1))) = (M.op (M.op X3 (σ (M.op X1 X1))) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq80676 X0 X1 x X3
       have i₂ := eq107 X1 x (σ X1)
       grind)
    | exact superpose eq107 eq80676
    | exact resolve eq80676 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq80676
  have eq80977 : ∀ X0 X2 X3 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X3) = (M.op (σ (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq80802 X0 X2 X3
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq80802
    | exact resolve eq80802 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80802
  have eq80996 : ∀ X0 X1 X3 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (M.op (M.op X3 (σ (M.op X1 X1))) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq80842 X0 X1 X3
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq80842
    | exact resolve eq80842 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80842
  have eq88113 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X3 (M.op (M.op X2 X1) X1)) (M.op (M.op X2 X1) X1))) = (M.op (σ (M.op (M.op (M.op X2 X1) X1) (M.op (M.op X2 X1) X1))) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64327 X3 (M.op (M.op X2 X1) X1)
       have i₂ := eq80489 X2 X1 X0
       grind)
    | (have i₁ := eq64327 X3 (M.op (M.op X2 X1) X1)
       have i₂ := eq80489 X0 X1 X2
       grind)
    | exact superpose eq80489 eq64327
    | exact resolve eq64327 eq80489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64327 eq80489
  have eq88114 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X3 (M.op (M.op X2 X1) X1)) (M.op (M.op X2 X1) X1))) = (M.op (M.op (σ X1) (σ (M.op X1 X1))) (σ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88113 X0 X1 X2 X3
       have i₂ := eq80977 X1 X2 (σ (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq80977 eq88113
    | exact resolve eq88113 eq80977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80977 eq88113
  have eq88292 : ∀ X1 X2 X3 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (σ (M.op (M.op X3 (M.op (M.op X2 X1) X1)) (M.op (M.op X2 X1) X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq88114 x X1 X2 X3
       have i₂ := eq80996 x X1 (σ X1)
       grind)
    | exact superpose eq80996 eq88114
    | exact resolve eq88114 eq80996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80996 eq88114
  have eq88380 : ∀ X1 : G, (M.op (σ X1) (σ (M.op X1 X1))) = (σ (M.op X1 (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq88292 X1 x x
       have i₂ := eq1777 X1 x (M.op x X1) X1 x
       grind)
    | exact superpose eq1777 eq88292
    | exact resolve eq88292 eq1777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777 eq88292
  have eq189395 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq6681
       grind)
    | exact superpose eq6681 eq10
    | exact resolve eq10 eq6681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6681
  have eq189404 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq189395
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq189395
    | exact resolve eq189395 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189395
  have eq189405 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq189404
  have eq189484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88380 x
       have i₂ := eq189405
       grind)
    | exact superpose eq189405 eq88380
    | exact resolve eq88380 eq189405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88380 eq189405
  have eq189633 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq189484
       have r₂ := eq16
       grind)
    | exact resolve eq189484 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189484
  have eq189652 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq189633
       grind)
    | exact superpose eq189633 eq10
    | exact resolve eq10 eq189633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189633
  have eq189756 : x = y ∨ x = y := by
    first
    | (have i₁ := eq189652
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq189652
    | exact resolve eq189652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189652
  have eq189757 : x = y := by grind
  clear eq189756
  have eq189765 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq189757
       grind)
    | exact superpose eq189757 eq16
    | exact resolve eq16 eq189757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189757
  have eq189766 : False := by grind
  exact eq189766

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation727 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law727 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X1) X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X0)) X1) = (M.op X0 (M.op X0 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 (M.op X2 X0)) X1) X0 X2
       have i₂ := eq25 X1 X0 X2 X3
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X0) x
       have i₂ := eq25 X1 X0 X2 x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq192 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq61
    | exact resolve eq61 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) X0)) = (M.op (M.op X1 X2) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X2 (M.op X2 (M.op (M.op X3 X2) X0)) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X2 (M.op (M.op X3 X2) X0) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X4 X3) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq60 X3 (M.op (M.op X4 X3) X0) X2 X1
       have i₂ := eq9 X0 X3 X4
       grind)
    | exact superpose eq9 eq60
    | exact resolve eq60 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1115 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq192 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq192
    | exact resolve eq192 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0)) = (M.op (σ (M.op X1 X1)) (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq192 X1 (M.op (σ X1) (M.op (σ (M.op X1 X1)) X0))
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq192
    | exact resolve eq192 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq192
  have eq1150 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1115 X0
       have i₂ := eq1117 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq1117 eq1115
    | exact resolve eq1115 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq1117
  have eq1160 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1150 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq1150
    | exact resolve eq1150 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1509 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1160 X1
       have i₂ := eq203 (M.op X1 X1) X1 X1 X0
       grind)
    | (have i₁ := eq1160 X1
       have i₂ := eq203 (M.op X1 X1) X0 X1 X1
       grind)
    | exact superpose eq203 eq1160
    | exact resolve eq1160 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq1160
  have eq1958 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq165 (τ X0) (τ X1)
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq165
    | (have j0 := eq165 (τ X0) (τ X1)
       grind)
    | exact resolve eq165 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq165
  have eq1966 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1958 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1958
    | (have j0 := eq1958 X0 X1
       grind)
    | exact resolve eq1958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq1969 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1966 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1966
    | (have j0 := eq1966 X0 X1
       grind)
    | exact resolve eq1966 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq1971 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1969 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1969
    | (have j0 := eq1969 X0 X1
       grind)
    | exact resolve eq1969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq1972 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1971 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1971
    | (have j0 := eq1971 X0 X1
       grind)
    | exact resolve eq1971 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq1973 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1972 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1972
    | (have j0 := eq1972 X0 X1
       grind)
    | exact resolve eq1972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972
  have eq1974 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1973 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1973
    | (have j0 := eq1973 X0 X1
       grind)
    | exact resolve eq1973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq4188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq159
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq159
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq159
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq159 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq4189 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4188
  have eq8005 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1509 x X0
       have i₂ := eq197 X0 x X0 X1
       grind)
    | exact superpose eq197 eq1509
    | exact resolve eq1509 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq1509
  have eq41574 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X0) X0)) = (M.op (σ (M.op (M.op X1 X0) X0)) (σ (M.op (M.op (M.op X1 X0) X0) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8005 (M.op (M.op X1 X0) X0) x
       have i₂ := eq920 X0 x (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq920 eq8005
    | exact resolve eq8005 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq8005
  have eq41848 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X0) X0)) = (M.op (σ (M.op (M.op X1 X0) X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41574 X0 X1
       have i₂ := eq61 X0 X0 (M.op X1 X0)
       grind)
    | exact superpose eq61 eq41574
    | exact resolve eq41574 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41574
  have eq122076 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4189
       grind)
    | exact superpose eq4189 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4189
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4189
       grind)
    | exact resolve eq13 eq4189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4189
  have eq122186 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq122076
  have eq122187 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq122186
  have eq122247 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq122187
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq122187
    | exact resolve eq122187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122187
  have eq1021648 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq122247
       grind)
    | exact superpose eq122247 eq10
    | exact resolve eq10 eq122247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122247
  have eq1021649 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1021648
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1021648
    | exact resolve eq1021648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021648
  have eq1021650 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1021649
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1021649 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021649
  have eq1021654 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1974 x y
       have i₂ := eq1021650
       grind)
    | exact superpose eq1021650 eq1974
    | (have j0 := eq1974 x y
       grind)
    | (have r₁ := eq1974 x y
       have r₂ := eq1021650
       grind)
    | exact resolve eq1974 eq1021650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974 eq1021650
  have eq1021657 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1021654
  have eq1021658 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1021657
  have eq1022286 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq1021658
       grind)
    | exact superpose eq1021658 eq9
    | exact resolve eq9 eq1021658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1023651 : y = (M.op y (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1022286 y
       have i₂ := eq1021658
       grind)
    | exact superpose eq1021658 eq1022286
    | exact resolve eq1022286 eq1021658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022286
  have eq1023690 : y = (M.op y (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1023651
  have eq1023701 : ∀ X0 : G, x = (M.op (M.op X0 y) y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq61 y x X0
       have i₂ := eq1023690
       grind)
    | exact superpose eq1023690 eq61
    | exact resolve eq61 eq1023690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1023690
  have eq1024741 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41848 y x
       have i₂ := eq1023701 x
       grind)
    | exact superpose eq1023701 eq41848
    | exact resolve eq41848 eq1023701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41848 eq1023701
  have eq1025173 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1024741
       grind)
    | exact superpose eq1024741 eq16
    | exact resolve eq16 eq1024741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024741
  have eq1025445 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1025173
       have i₂ := eq1021658
       grind)
    | exact superpose eq1021658 eq1025173
    | exact resolve eq1025173 eq1021658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021658 eq1025173
  have eq1025446 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1025445
  have eq1025447 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1025446
  have eq1025677 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1025447
       grind)
    | exact superpose eq1025447 eq10
    | exact resolve eq10 eq1025447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025447
  have eq1025986 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1025677
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1025677
    | exact resolve eq1025677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025677
  have eq1025987 : x = y := by grind
  clear eq1025986
  have eq1026424 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1025987
       grind)
    | exact superpose eq1025987 eq16
    | exact resolve eq16 eq1025987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025987
  have eq1026425 : False := by grind
  exact eq1026425

/-- `Equation829`: `x = x ◇ ((x ◇ y) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,Y) = Y then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_x_pxy_x_Equation829 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law829 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law829.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X2 X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X2) (M.op (M.op X0 (M.op X1 X2)) X2)
       have i₂ := eq9 (M.op X0 (M.op X1 X2)) X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0 (M.op x x)
       have i₂ := eq24 X0 x x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq44 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq177 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq47 (τ X1) X0
       grind)
    | exact superpose eq47 eq19
    | (have j1 := eq47 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq178 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq47 (σ X1) (σ X0)
       grind)
    | exact superpose eq47 eq15
    | (have j1 := eq47 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq563 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq589 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq563
    | (have j0 := eq563 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq563 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq1248 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq178 x y
       grind)
    | exact superpose eq178 eq16
    | (have j1 := eq178 x y
       grind)
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1248
       have i₂ := eq589 y x
       grind)
    | exact superpose eq589 eq1248
    | (have j1 := eq589 (σ x) (σ y)
       grind)
    | (have r₁ := eq1248
       have r₂ := eq589 y x
       grind)
    | (have r₁ := eq1248
       have r₂ := eq589 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1248
       have r₂ := eq589 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1248 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq1248
  have eq1380 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1379
  have eq1480 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1380
       grind)
    | exact superpose eq1380 eq10
    | exact resolve eq10 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq1517 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1480
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1480
    | exact resolve eq1480 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480
  have eq1518 : x = y := by grind
  clear eq1517
  have eq1619 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1518
       grind)
    | exact superpose eq1518 eq16
    | exact resolve eq16 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1620 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1619
       have i₂ := eq28 x
       grind)
    | exact superpose eq28 eq1619
    | exact resolve eq1619 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619
  have eq1621 : False := by grind
  exact eq1621

/-- `Equation834`: `x = x ◇ ((y ◇ x) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation834 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law834 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law834.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq81 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42 x y
       grind)
    | exact superpose eq42 eq16
    | (have j1 := eq42 x y
       grind)
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq511 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43
    | exact resolve eq43 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq552 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq511
    | (have j0 := eq511 X0 X1
       grind)
    | exact resolve eq511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq1067 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq81
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq81
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq81
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq81
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq81 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1068 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1067
  have eq8120 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1068
       grind)
    | exact superpose eq1068 eq16
    | exact resolve eq16 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8138 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1068
       grind)
    | exact superpose eq1068 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1068
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1068
       grind)
    | exact resolve eq13 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq8162 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8138
  have eq8163 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8162
  have eq8169 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8163
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8163
    | exact resolve eq8163 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8163
  have eq14444 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq552 x y
       have i₂ := eq8169
       grind)
    | exact superpose eq8169 eq552
    | (have j0 := eq552 x y
       grind)
    | exact resolve eq552 eq8169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq14445 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq8169
       grind)
    | exact superpose eq8169 eq10
    | exact resolve eq10 eq8169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8169
  have eq14510 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14444
  have eq14545 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14445
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14445
    | exact resolve eq14445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14445
  have eq14546 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14510
       have r₂ := eq8120
       grind)
    | exact resolve eq14510 eq8120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8120 eq14510
  have eq14549 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq14545
       have r₂ := eq13 x y
       grind)
    | exact resolve eq14545 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14545
  have eq14975 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq86 x y
       have i₂ := eq14549
       grind)
    | exact superpose eq14549 eq86
    | (have j0 := eq86 x y
       grind)
    | exact resolve eq86 eq14549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq14549
  have eq14993 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14975
  have eq14994 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14993
  have eq15492 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq14994
       grind)
    | exact superpose eq14994 eq16
    | exact resolve eq16 eq14994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14994
  have eq15682 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15492
       have i₂ := eq14546
       grind)
    | exact superpose eq14546 eq15492
    | exact resolve eq15492 eq14546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14546 eq15492
  have eq15683 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15682
  have eq15684 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq15683
  have eq15886 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15684
       grind)
    | exact superpose eq15684 eq10
    | exact resolve eq10 eq15684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684
  have eq15988 : x = y ∨ x = y := by
    first
    | (have i₁ := eq15886
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15886
    | exact resolve eq15886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15886
  have eq15989 : x = y := by grind
  clear eq15988
  have eq16191 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15989
       grind)
    | exact superpose eq15989 eq16
    | exact resolve eq16 eq15989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15989
  have eq16192 : False := by grind
  exact eq16192

/-- `Equation834`: `x = x ◇ ((y ◇ x) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation834 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law834 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law834.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq45 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq110 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq16
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq734 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq770 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq110
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq110
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq110
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq110
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq110 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1286 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1285
  have eq8816 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1286
       grind)
    | exact superpose eq1286 eq16
    | exact resolve eq16 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8834 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1286
       grind)
    | exact superpose eq1286 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1286
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1286
       grind)
    | exact resolve eq13 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq8867 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8834
  have eq8868 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8867
  have eq8872 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8868
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8868
    | exact resolve eq8868 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8868
  have eq16334 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq770 y x
       have i₂ := eq8872
       grind)
    | exact superpose eq8872 eq770
    | (have j0 := eq770 y x
       grind)
    | exact resolve eq770 eq8872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq8872
  have eq16403 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16334
  have eq16438 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16403
       have r₂ := eq8816
       grind)
    | exact resolve eq16403 eq8816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8816 eq16403
  have eq16640 : x ≠ x ∨ x = y ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16438
       grind)
    | exact superpose eq16438 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16438
       grind)
    | exact resolve eq13 eq16438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16683 : x ≠ x ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq16640
  have eq16684 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16683
  have eq16934 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117 x y
       have i₂ := eq16684
       grind)
    | exact superpose eq16684 eq117
    | (have j0 := eq117 x y
       grind)
    | exact resolve eq117 eq16684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq16684
  have eq16952 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16934
  have eq16953 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16952
  have eq18149 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq16953
       grind)
    | exact superpose eq16953 eq16
    | exact resolve eq16 eq16953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16953
  have eq18375 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18149
       have i₂ := eq16438
       grind)
    | exact superpose eq16438 eq18149
    | exact resolve eq18149 eq16438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16438 eq18149
  have eq18376 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18375
  have eq18377 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq18376
  have eq18754 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18377
       grind)
    | exact superpose eq18377 eq10
    | exact resolve eq10 eq18377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18377
  have eq18865 : x = y ∨ x = y := by
    first
    | (have i₁ := eq18754
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18754
    | exact resolve eq18754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18754
  have eq18866 : x = y := by grind
  clear eq18865
  have eq19032 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18866
       grind)
    | exact superpose eq18866 eq16
    | exact resolve eq16 eq18866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18866
  have eq19033 : False := by grind
  exact eq19033
