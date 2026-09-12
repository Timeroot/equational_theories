import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_pyy_pyx_Equation1027 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 X0 (M.op X0 x)
       have i₂ := eq63 X0 x
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq83 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq66 X0
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq84 (σ X1) (σ X0)
       grind)
    | exact superpose eq84 eq15
    | exact resolve eq15 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq84 X1 X0
       grind)
    | exact superpose eq84 eq87
    | exact resolve eq87 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq87
  have eq266 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98 x y
       grind)
    | exact superpose eq98 eq16
    | (have r₁ := eq16
       have r₂ := eq98 x y
       grind)
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq274 : False := by grind
  exact eq274

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = X then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_x_pxy_y_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq75 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 X0 (M.op X0 x)
       have i₂ := eq75 X0 x
       grind)
    | exact superpose eq75 eq75
    | exact resolve eq75 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq103 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq78 X0
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq104 X0 (τ X1)
       grind)
    | exact superpose eq104 eq19
    | (have j1 := eq104 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq104 (σ X0) (σ X1)
       grind)
    | exact superpose eq104 eq15
    | (have j1 := eq104 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq141 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq159 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq141
    | (have j0 := eq141 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq600 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110 x y
       grind)
    | exact superpose eq110 eq16
    | (have j1 := eq110 x y
       grind)
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq614 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq600
       have i₂ := eq159 y x
       grind)
    | exact superpose eq159 eq600
    | (have j1 := eq159 (σ x) (σ y)
       grind)
    | (have r₁ := eq600
       have r₂ := eq159 y x
       grind)
    | (have r₁ := eq600
       have r₂ := eq159 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq600
       have r₂ := eq159 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq600 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq600
  have eq615 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq614
  have eq654 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq615
       grind)
    | exact superpose eq615 eq16
    | exact resolve eq16 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq655 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq654
       have i₂ := eq78 (σ x)
       grind)
    | exact superpose eq78 eq654
    | exact resolve eq654 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq656 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq655
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq655
    | exact resolve eq655 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq657 : (σ x) = (σ y) := by grind
  clear eq656
  have eq658 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq657
       grind)
    | exact superpose eq657 eq16
    | exact resolve eq16 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq657
       grind)
    | exact superpose eq657 eq10
    | exact resolve eq10 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq696 : x = y := by
    first
    | (have i₁ := eq659
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq659
    | exact resolve eq659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq697 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq658
       have i₂ := eq78 (σ x)
       grind)
    | exact superpose eq78 eq658
    | exact resolve eq658 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq698 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq697
       have i₂ := eq696
       grind)
    | exact superpose eq696 eq697
    | exact resolve eq697 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq697
  have eq699 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq698
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq698
    | exact resolve eq698 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq698
  have eq700 : False := by grind
  exact eq700

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pxy_pxx_Equation1027 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law1027 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq109 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 X0 (M.op X0 x)
       have i₂ := eq109 X0 x
       grind)
    | exact superpose eq109 eq109
    | exact resolve eq109 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq143 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq114 X0
       grind)
    | exact resolve eq13 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq148 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq144 (τ X1) X0
       grind)
    | exact superpose eq144 eq19
    | (have j1 := eq144 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq144 (σ X1) (σ X0)
       grind)
    | exact superpose eq144 eq15
    | (have j1 := eq144 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq199 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq964 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq149 x y
       grind)
    | exact superpose eq149 eq16
    | (have j1 := eq149 x y
       grind)
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq991 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq964
       have i₂ := eq219 y x
       grind)
    | exact superpose eq219 eq964
    | (have j1 := eq219 (σ x) (σ y)
       grind)
    | (have r₁ := eq964
       have r₂ := eq219 y x
       grind)
    | (have r₁ := eq964
       have r₂ := eq219 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq964
       have r₂ := eq219 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq964 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq964
  have eq992 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq991
  have eq994 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq16
    | exact resolve eq16 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq995 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq994
       have r₂ := eq22 x
       grind)
    | exact resolve eq994 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq994
  have eq996 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq995
       grind)
    | exact superpose eq995 eq16
    | exact resolve eq16 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq995
       grind)
    | exact superpose eq995 eq10
    | exact resolve eq10 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1038 : x = y := by
    first
    | (have i₁ := eq997
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq997
    | exact resolve eq997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1039 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq996
       have i₂ := eq114 (σ x)
       grind)
    | exact superpose eq114 eq996
    | exact resolve eq996 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1042 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1039
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq1039
    | exact resolve eq1039 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq1039
  have eq1044 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1042
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq1042
    | exact resolve eq1042 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1042
  have eq1045 : False := by grind
  exact eq1045

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq105 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq560 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 X1
       have i₂ := eq88 X1
       grind)
    | exact superpose eq88 eq543
    | (have j0 := eq543 X0 X1
       grind)
    | exact resolve eq543 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq571 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq560
    | exact resolve eq560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq599 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq571
    | (have j0 := eq571 X0 X1
       grind)
    | exact resolve eq571 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq571
  have eq606 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq599 X0 X1
       have j1 := eq105 X1 X0
       grind)
    | (have r₁ := eq599 X1 X0
       have r₂ := eq105 X0 X1
       grind)
    | (have r₁ := eq599 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq599 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq599
  have eq612 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq606
    | exact resolve eq606 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq606 (σ X0) X1
       grind)
    | exact superpose eq606 eq15
    | (have j1 := eq606 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq652 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq612 (τ X1) X0
       grind)
    | exact superpose eq612 eq19
    | (have j1 := eq612 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq612
  have eq735 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq652
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq783 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq735
    | (have j0 := eq735 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq735 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq1245 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq623 x y
       grind)
    | exact superpose eq623 eq16
    | (have j1 := eq623 x y
       grind)
    | exact resolve eq16 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq1265 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1245
       have i₂ := eq783 y x
       grind)
    | exact superpose eq783 eq1245
    | (have j1 := eq783 (σ x) (σ y)
       grind)
    | (have r₁ := eq1245
       have r₂ := eq783 y x
       grind)
    | (have r₁ := eq1245
       have r₂ := eq783 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1245
       have r₂ := eq783 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1245 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq1245
  have eq1266 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1265
  have eq1269 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1266
       grind)
    | exact superpose eq1266 eq16
    | exact resolve eq16 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1270 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1269
       have r₂ := eq88 x
       grind)
    | exact resolve eq1269 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1271 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1270
       grind)
    | exact superpose eq1270 eq16
    | exact resolve eq16 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1272 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1270
       grind)
    | exact superpose eq1270 eq10
    | exact resolve eq10 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1318 : x = y := by
    first
    | (have i₁ := eq1272
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1272
    | exact resolve eq1272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1319 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1271
       have i₂ := eq88 x
       grind)
    | exact superpose eq88 eq1271
    | exact resolve eq1271 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1271
  have eq1320 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1319
       have i₂ := eq1318
       grind)
    | exact superpose eq1318 eq1319
    | exact resolve eq1319 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq1319
  have eq1321 : False := by grind
  exact eq1321

/-- `Equation1031`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation1031 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1031 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1031.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq43 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq43
    | exact resolve eq43 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq59 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq85 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq116 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq126 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 X0 X1 X2
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq116
    | (have j0 := eq116 X0 X1 X2
       grind)
    | exact resolve eq116 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq116
  have eq3123 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k X3 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq126 X0 X1 X2
       grind)
    | exact superpose eq126 eq13
    | (have j0 := eq13 (M.op (σ X0) (k (σ X1) X2)) (k X3 (k (σ X1) X2))
       have j1 := eq126 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq126 X0 X1 X2
       grind)
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq226798 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3123 X0 X1 X2 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3123
  have eq226799 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq226798 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226798
  have eq226812 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq226799 X0 X1 X2
       have i₂ := eq35 X1 X2 X0
       grind)
    | exact superpose eq35 eq226799
    | (have j0 := eq226799 X0 X1 X2
       grind)
    | exact resolve eq226799 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq226799
  have eq226813 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq226812 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226812
  have eq227336 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq226813 (τ X0) X1 X2
       grind)
    | exact superpose eq226813 eq18
    | (have j1 := eq226813 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq226813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226813
  have eq227686 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq227336 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227336
    | (have j0 := eq227336 X0 X1 X2
       grind)
    | exact resolve eq227336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227336
  have eq227837 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq227686 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq227686
    | (have j0 := eq227686 X0 X1 X2
       grind)
    | exact resolve eq227686 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq227686
  have eq227964 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq227837 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227837
    | (have j0 := eq227837 X0 X1 X2
       grind)
    | exact resolve eq227837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227837
  have eq228224 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op X1 (k X0 X2)) ∨ (k X0 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq227964 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq227964
    | exact resolve eq227964 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228334 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ X0))) = (k X1 (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    grind
  clear eq227964
  have eq228905 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k X1 (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq228334 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq228334
    | (have j0 := eq228334 X0 X1
       grind)
    | exact resolve eq228334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228334
  have eq228941 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (k X1 (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq228905 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq228905
    | (have j0 := eq228905 X0 X1
       grind)
    | exact resolve eq228905 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228905
  have eq230044 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 X2))) = (σ (M.op (τ X0) (k X1 X2))) ∨ (τ X0) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 X2)
       have i₂ := eq228224 X1 (τ X0) X2
       grind)
    | exact superpose eq228224 eq18
    | (have j1 := eq228224 X0 (σ (M.op (τ X0) (k X1 X2))) (σ (k X1 X2))
       grind)
    | exact resolve eq18 eq228224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq234404 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 (σ (M.op X1 X1)))) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq228941 X1 X0
       grind)
    | exact superpose eq228941 eq28
    | (have j1 := eq228941 X1 X0
       grind)
    | exact resolve eq28 eq228941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228941
  have eq241706 : ∀ X0 X1 X2 : G, (σ (M.op X0 (k X1 X2))) = (k (σ X0) (σ (k X1 X2))) ∨ (k X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq230044 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq230044
    | exact resolve eq230044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230044
  have eq242235 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 X2))) = (σ (M.op X0 (k X1 X2))) ∨ (k X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq241706 X0 X1 X2
       have i₂ := eq15 X0 (k X1 X2)
       grind)
    | exact superpose eq15 eq241706
    | (have j0 := eq241706 X0 X1 X2
       grind)
    | exact resolve eq241706 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241706
  have eq244430 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq234404 (σ X0) X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq234404
    | (have j0 := eq234404 (σ X0) X0
       grind)
    | exact resolve eq234404 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq234404
  have eq244766 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq244430 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq244430
    | (have j0 := eq244430 X0
       grind)
    | exact resolve eq244430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244430
  have eq245756 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq244766 X0
       grind)
    | exact superpose eq244766 eq10
    | (have j1 := eq244766 X0
       grind)
    | exact resolve eq10 eq244766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245764 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op X0 X0)
       have i₂ := eq244766 X0
       grind)
    | exact superpose eq244766 eq28
    | (have j1 := eq244766 X0
       grind)
    | exact resolve eq28 eq244766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244766
  have eq246132 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq245764 X0 X1
       have i₂ := eq28 X1 X0
       grind)
    | exact superpose eq28 eq245764
    | (have j0 := eq245764 X0 X1
       grind)
    | exact resolve eq245764 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq245764
  have eq246140 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq245756 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq245756
    | (have j0 := eq245756 X0
       grind)
    | exact resolve eq245756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245756
  have eq262072 : ∀ X0 : G, (τ X0) ≠ (k (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq246132 (τ X0) x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246132
  have eq262073 : ∀ X0 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq262072
  have eq262138 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq262073 X0
       have j1 := eq246140 (τ X0)
       grind)
    | (have r₁ := eq262073 X0
       have r₂ := eq246140 (τ X0)
       grind)
    | exact resolve eq262073 eq246140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246140 eq262073
  have eq262145 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq262138 X0
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq262138
    | exact resolve eq262138 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq262138
  have eq262152 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq262145 X0
       have i₂ := eq59 (M.op X0 X0) X0
       grind)
    | exact superpose eq59 eq262145
    | exact resolve eq262145 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq262145
  have eq262313 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (M.op X0 X0))
       have i₂ := eq262152 X0
       grind)
    | exact superpose eq262152 eq11
    | exact resolve eq11 eq262152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262152
  have eq262656 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq262313 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq262313
    | exact resolve eq262313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262313
  have eq263788 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq228224 X0 X1 (M.op X0 X0)
       have i₂ := eq262656 X0
       grind)
    | exact superpose eq262656 eq228224
    | (have j0 := eq228224 X1 (M.op X1 X0) X0
       grind)
    | exact resolve eq228224 eq262656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228224
  have eq263795 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq242235 X0 X0 (M.op X0 X0)
       have i₂ := eq262656 X0
       grind)
    | exact superpose eq262656 eq242235
    | exact resolve eq242235 eq262656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242235 eq262656
  have eq265258 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq263788 (σ X1) (σ X0)
       grind)
    | exact superpose eq263788 eq15
    | (have j1 := eq263788 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq263788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263788
  have eq285371 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq265258 x y
       grind)
    | exact superpose eq265258 eq16
    | (have j1 := eq265258 x y
       grind)
    | exact resolve eq16 eq265258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265258
  have eq286784 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq285371
       have i₂ := eq263795 y x
       grind)
    | exact superpose eq263795 eq285371
    | (have j1 := eq263795 (σ x) (σ y)
       grind)
    | (have r₁ := eq285371
       have r₂ := eq263795 y x
       grind)
    | (have r₁ := eq285371
       have r₂ := eq263795 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq285371
       have r₂ := eq263795 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq285371 eq263795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263795 eq285371
  have eq286787 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq286784
  have eq286790 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286787
       grind)
    | exact superpose eq286787 eq16
    | exact resolve eq16 eq286787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286787
  have eq286791 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq286790
       have r₂ := eq22 x
       grind)
    | exact resolve eq286790 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286790
  have eq287984 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq286791
       grind)
    | exact superpose eq286791 eq16
    | exact resolve eq16 eq286791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287985 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq286791
       grind)
    | exact superpose eq286791 eq10
    | exact resolve eq10 eq286791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286791
  have eq288387 : x = y := by
    first
    | (have i₁ := eq287985
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq287985
    | exact resolve eq287985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287985
  have eq288388 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq287984
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq287984
    | exact resolve eq287984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq287984
  have eq288393 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq288388
       have i₂ := eq288387
       grind)
    | exact superpose eq288387 eq288388
    | exact resolve eq288388 eq288387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288387 eq288388
  have eq288394 : False := by grind
  exact eq288394

/-- `Equation1060`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation1060 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1060 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1060.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 (M.op x X0))
       have i₂ := eq14 X0 X0 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq101 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq102 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq106 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq109
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq106
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq187 : (σ (k (k x x) y)) = (k (k (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq40 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq40
    | exact resolve eq40 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq841 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq100 X0 X0
       grind)
    | exact superpose eq100 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq100 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq100 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq100 X0 X1
       grind)
    | exact resolve eq13 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq100 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq845 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq848 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq852 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq848 X0 X1
       have j1 := eq13 (σ X0) X1
       grind)
    | (have r₁ := eq848 X0 X1
       have r₂ := eq13 (σ X0) X1
       grind)
    | exact resolve eq848 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq4451 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq845 (M.op X0 X0)
       have i₂ := eq74 X0 (M.op X0 X0)
       grind)
    | exact superpose eq74 eq845
    | (have j0 := eq845 (M.op X0 X0)
       grind)
    | exact resolve eq845 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq4482 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4451 X0
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq4451
    | (have j0 := eq4451 X0
       grind)
    | exact resolve eq4451 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451
  have eq4483 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4482 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4482
  have eq5213 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq852 (M.op X0 X0) X1
       have i₂ := eq74 X0 (M.op X0 X0)
       grind)
    | exact superpose eq74 eq852
    | (have j0 := eq852 (M.op X0 X0) X1
       grind)
    | exact resolve eq852 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq5248 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5213 X0 X1
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq5213
    | (have j0 := eq5213 X0 X1
       grind)
    | exact resolve eq5213 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5213
  have eq5249 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq5248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5248
  have eq6718 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq101 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101
    | (have j0 := eq101 x
       grind)
    | exact resolve eq101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq6730 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6718
  have eq6733 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6730
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6730
    | exact resolve eq6730 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6730
  have eq6748 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6733
       have r₂ := eq13 (σ x) x
       grind)
    | exact resolve eq6733 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6733
  have eq6752 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6748 eq49
    | exact resolve eq49 eq6748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq6897 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102
    | (have j0 := eq102 y
       grind)
    | exact resolve eq102 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq6908 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6897
  have eq6910 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6908
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq6908
    | exact resolve eq6908 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq6908
  have eq6932 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6910
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq6910 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6910
  have eq6951 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6932 eq99
    | exact resolve eq99 eq6932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq13759 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6932 eq115
    | exact resolve eq115 eq6932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq6932
  have eq13760 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6748 eq116
    | exact resolve eq116 eq6748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq19398 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq13759
       grind)
    | exact superpose eq13759 eq16
    | exact resolve eq16 eq13759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13759
  have eq19472 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6951 eq19398
    | exact resolve eq19398 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19398
  have eq19493 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq19472
       have r₂ := eq13 y x
       grind)
    | exact resolve eq19472 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19472
  have eq19681 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq13760
       grind)
    | exact superpose eq13760 eq16
    | exact resolve eq16 eq13760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13760
  have eq19755 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6752 eq19681
    | exact resolve eq19681 eq6752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19681
  have eq19777 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq19755
       have r₂ := eq13 x x
       grind)
    | exact resolve eq19755 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19755
  have eq19798 : (k (k (σ x) (σ x)) (σ y)) = (σ (k (M.op x x) y)) := by
    first
    | (have i₁ := eq187
       have i₂ := eq19777
       grind)
    | exact superpose eq19777 eq187
    | exact resolve eq187 eq19777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq19840 : (k (k (σ x) (σ x)) (σ y)) = (σ (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq19798
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq19798
    | exact resolve eq19798 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19798
  have eq19857 : (σ (M.op (M.op x x) y)) = (k (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq6748 eq19840
    | exact resolve eq19840 eq6748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6748 eq19840
  have eq19861 : (σ (M.op (M.op x x) y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq19857
       have i₂ := eq74 sF2 sF3
       grind)
    | exact superpose eq74 eq19857
    | exact resolve eq19857 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19857
  have eq32633 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ (M.op X0 X0)) X1
       have i₂ := eq4483 X0
       grind)
    | exact superpose eq4483 eq53
    | exact resolve eq53 eq4483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4483
  have eq42757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq42758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq42757
    | exact resolve eq42757 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42757
  have eq42769 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq42758
       have r₂ := eq27
       grind)
    | exact resolve eq42758 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42758
  have eq42773 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq42769 eq6951
    | exact resolve eq6951 eq42769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951 eq42769
  have eq42845 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq42773
       have i₂ := eq19493
       grind)
    | exact superpose eq19493 eq42773
    | exact resolve eq42773 eq19493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19493 eq42773
  have eq42854 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq42845
    | exact resolve eq42845 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq42845
  have eq42855 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq42854
  have eq42858 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq42855 eq6752
    | exact resolve eq6752 eq42855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752 eq42855
  have eq42930 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq42858
       have i₂ := eq19777
       grind)
    | exact superpose eq19777 eq42858
    | exact resolve eq42858 eq19777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19777 eq42858
  have eq42939 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq42930
    | exact resolve eq42930 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq42930
  have eq42940 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq42939
  have eq42962 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y X0
       have i₂ := eq42940
       grind)
    | exact superpose eq42940 eq53
    | exact resolve eq53 eq42940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42975 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq32633 y X0
       have i₂ := eq42940
       grind)
    | exact superpose eq42940 eq32633
    | exact resolve eq32633 eq42940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42940
  have eq43018 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq42975 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42975
    | (have j0 := eq42975 X0
       grind)
    | exact resolve eq42975 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq42975
  have eq43050 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq42962 X1
       grind)
    | exact superpose eq42962 eq53
    | (have j1 := eq42962 X1
       grind)
    | exact resolve eq53 eq42962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42962
  have eq43140 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq43018 X1
       grind)
    | exact superpose eq43018 eq53
    | (have j1 := eq43018 X1
       grind)
    | exact resolve eq53 eq43018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq43018
  have eq43212 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq43050 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43050
    | (have j0 := eq43050 X0 x
       grind)
    | exact resolve eq43050 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43050
  have eq43420 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74 x x
       have i₂ := eq43212 x
       grind)
    | exact superpose eq43212 eq74
    | exact resolve eq74 eq43212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq43428 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5249 x x
       have i₂ := eq43212 x
       grind)
    | exact superpose eq43212 eq5249
    | exact resolve eq5249 eq43212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5249 eq43212
  have eq43600 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq43428 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43428
    | (have j0 := eq43428 X0
       grind)
    | exact resolve eq43428 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43428
  have eq45418 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq43140
    | (have j0 := eq43140 X0 (σ x)
       grind)
    | exact resolve eq43140 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46134 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32633 x X0
       have i₂ := eq45418 x
       grind)
    | exact superpose eq45418 eq32633
    | exact resolve eq32633 eq45418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32633 eq45418
  have eq46300 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq46134 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46134
    | (have j0 := eq46134 X0
       grind)
    | exact resolve eq46134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46134
  have eq49482 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq43420 y
       grind)
    | exact superpose eq43420 eq44
    | exact resolve eq44 eq43420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq43420
  have eq49508 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49482
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq49482
    | exact resolve eq49482 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49482
  have eq49553 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq49508
    | exact resolve eq49508 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49508
  have eq50593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43600 eq49553
    | exact resolve eq49553 eq43600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43600 eq49553
  have eq50594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq50593
  have eq50596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq50594
    | exact resolve eq50594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50594
  have eq50625 : x = (M.op x y) := by
    first
    | (have r₁ := eq50596
       have r₂ := eq27
       grind)
    | exact resolve eq50596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50596
  have eq50642 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq50625 eq20
    | exact resolve eq20 eq50625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50625
  have eq50822 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq50642
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50642
    | exact resolve eq50642 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50642
  have eq50881 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq50822 eq26
    | exact resolve eq26 eq50822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq50976 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq50822 eq46300
    | exact resolve eq46300 eq50822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46300
  have eq50978 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq50976 X0
       grind)
    | (have r₁ := eq50976 X0
       have r₂ := eq27
       grind)
    | exact resolve eq50976 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50976
  have eq51131 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq50881 eq43140
    | (have j0 := eq43140 X0 x
       grind)
    | exact resolve eq43140 eq50881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43140
  have eq51145 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq51131 X0
       grind)
    | (have r₁ := eq51131 X0
       have r₂ := eq27
       grind)
    | exact resolve eq51131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51131
  have eq52295 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq19861
       have i₂ := eq51145 x
       grind)
    | exact superpose eq51145 eq19861
    | exact resolve eq19861 eq51145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19861 eq51145
  have eq52309 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq50822 eq52295
    | exact resolve eq52295 eq50822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50822 eq52295
  have eq52369 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq50978 eq52309
    | exact resolve eq52309 eq50978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50978 eq52309
  have eq52399 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50881 eq52369
    | exact resolve eq52369 eq50881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50881 eq52369
  have eq52406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52399
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52399
    | exact resolve eq52399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52399
  have eq52411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq52406
    | exact resolve eq52406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq52406
  have eq52415 : False := by grind
  exact eq52415

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_y_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq92 y x
       grind)
    | exact superpose eq92 eq72
    | (have j1 := eq92 y x
       grind)
    | exact resolve eq72 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq116 eq92
    | (have j0 := eq92 (σ y) x
       grind)
    | exact resolve eq92 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq701
    | exact resolve eq701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq705 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq702
       have r₂ := eq27
       grind)
    | exact resolve eq702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq712 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq705 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq705
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq705
       grind)
    | exact resolve eq13 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq712 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq753 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq713 eq86
    | exact resolve eq86 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq713
  have eq844 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq705 eq753
    | exact resolve eq753 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq753
  have eq857 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq844
  have eq859 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq857
    | exact resolve eq857 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq857
  have eq862 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq92 y y
       have i₂ := eq859
       grind)
    | exact superpose eq859 eq92
    | (have j0 := eq92 y x
       grind)
    | exact resolve eq92 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq863 : y = (M.op y y) := by grind
  clear eq862
  have eq870 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq863
       grind)
    | exact superpose eq863 eq14
    | exact resolve eq14 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq863
       grind)
    | exact superpose eq863 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq863
       grind)
    | exact resolve eq13 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq875 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq870 X0
       have i₂ := eq863
       grind)
    | exact superpose eq863 eq870
    | exact resolve eq870 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq880 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq875 X0
       have i₂ := eq863
       grind)
    | exact superpose eq863 eq875
    | exact resolve eq875 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq875
  have eq885 : x = (M.op x y) := by
    first
    | (have i₁ := eq880 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq880
    | (have j0 := eq880 x
       grind)
    | exact resolve eq880 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq943 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq885 eq20
    | exact resolve eq20 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq885
  have eq962 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq943
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq943
    | exact resolve eq943 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq943
  have eq963 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq962 eq26
    | exact resolve eq26 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq962
  have eq997 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq873 y
       grind)
    | exact superpose eq873 eq73
    | exact resolve eq73 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq873
  have eq1006 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq997
       have i₂ := eq880 y
       grind)
    | exact superpose eq880 eq997
    | exact resolve eq997 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq997
  have eq1008 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1006
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1006
    | exact resolve eq1006 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1006
  have eq1080 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1008 eq92
    | (have j0 := eq92 (σ y) x
       grind)
    | exact resolve eq92 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1008
  have eq1081 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1080
  have eq1093 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq1081 eq14
    | exact resolve eq14 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq1081 eq1093
    | exact resolve eq1093 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1102 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1081 eq1096
    | exact resolve eq1096 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq1096
  have eq1129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1102 eq963
    | exact resolve eq963 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq1102
  have eq1135 : False := by grind
  exact eq1135

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pyx_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq14 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq66 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq65
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq110
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq111 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq141 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37
  have eq229 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ x)) (σ x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq51
    | exact resolve eq51 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq130
  have eq238 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq249 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op (σ x) (M.op (σ y) (σ x))) X0))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f249_11 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
      intro X0
      grind
    have f249_16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
      intro X0 X1 X2
      grind
    have f249_17 : X1 ≠ (M.op X1 (M.op X0 (M.op (M.op (σ x) (M.op (σ y) (σ x))) X0))) := by grind
    have f249_18 : x ≠ (M.op x y) := by grind
    have f249_20 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f249_11 X0
         grind)
      | (have r₁ := f249_11 X0
         have r₂ := f249_18
         grind)
      | exact resolve f249_11 f249_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f249_69 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op (σ x) (M.op (σ y) (σ x))) X0))) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f249_16 X1 X0 (M.op (σ x) (M.op (σ y) (σ x)))
         have i₂ := f249_20 (M.op X0 (M.op (M.op (σ x) (M.op (σ y) (σ x))) X0))
         grind)
      | exact superpose f249_20 f249_16
      | exact resolve f249_16 f249_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f249_419 : X1 ≠ X1 := by
      first
      | (have i₁ := f249_17
         have i₂ := f249_69 X0 X1
         grind)
      | exact superpose f249_69 f249_17
      | (have r₁ := f249_17
         have r₂ := f249_69 X0 X1
         grind)
      | exact resolve f249_17 f249_69
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f249_420 : False := by grind
    exact f249_420
  clear eq238
  have eq411 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq249 sF3 x
       have i₂ := eq14 sF3 sF2 sF3
       grind)
    | exact superpose eq14 eq249
    | exact resolve eq249 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq442 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq411 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq411 (σ y)
       grind)
    | exact resolve eq13 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq460 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq442 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq460 eq111
    | exact resolve eq111 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq460
  have eq469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq465
  have eq472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq469
    | exact resolve eq469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq474 : x = (M.op x y) := by
    first
    | (have r₁ := eq472
       have r₂ := eq27
       grind)
    | exact resolve eq472 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq522 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq474 eq20
    | exact resolve eq20 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq522
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq522
    | exact resolve eq522 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq522
  have eq535 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq534 eq26
    | exact resolve eq26 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq534
  have eq578 : ∀ X0 : G, (k X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq66
    | exact resolve eq66 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq66
  have eq605 : ∀ X0 : G, (k X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | exact superpose eq474 eq578
    | exact resolve eq578 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq578
  have eq826 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ (M.op X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 X0 (M.op x (M.op y x))
       have i₂ := eq605 X0
       grind)
    | exact superpose eq605 eq76
    | (have j0 := eq76 X0 (M.op x (M.op y x))
       grind)
    | exact resolve eq76 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq828 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | (have j0 := eq826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq889 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y X0 x
       have i₂ := eq828 y
       grind)
    | exact superpose eq828 eq53
    | exact resolve eq53 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq828
  have eq922 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq889 y
       grind)
    | exact superpose eq889 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq889 y
       grind)
    | exact resolve eq13 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq948 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq944 X0
       have i₂ := eq889 X0
       grind)
    | exact superpose eq889 eq944
    | exact resolve eq944 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq944
  have eq956 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq141
       have i₂ := eq948 sF0
       grind)
    | exact superpose eq948 eq141
    | exact resolve eq141 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq948
  have eq964 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq956
    | exact resolve eq956 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq956
  have eq975 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq964 eq76
    | (have j0 := eq76 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq76 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq964
  have eq976 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq975
  have eq978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq535 eq976
    | exact resolve eq976 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq976
  have eq981 : False := by grind
  exact eq981
