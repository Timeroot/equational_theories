import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation168`: `x = (y ◇ x) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_y_Equation168 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) Law168 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law168.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq42 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq25
    | exact resolve eq25 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39
  have eq43 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq42
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq48 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq33 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq33 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq48 eq9
    | exact resolve eq9 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq64 : ∀ X1 : G, (M.op x y) = (M.op (τ (σ x)) (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op x x) X1
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (k (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 X0) (M.op X0 X2)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (k (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (k (M.op X1 X0) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 X1 X2
       have i₂ := eq71 (M.op X1 X0)
       grind)
    | exact superpose eq71 eq66
    | (have j0 := eq66 X0 X1 X2
       grind)
    | exact resolve eq66 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq77 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) ≠ X0 ∨ (k (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq82 : ∀ X0 X1 X2 : G, (k (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76 X0 X1 X2
       have i₂ := eq71 (M.op X1 X0)
       grind)
    | exact superpose eq71 eq76
    | (have j0 := eq76 X0 X1 X2
       grind)
    | exact resolve eq76 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq83 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) ≠ X0 ∨ (k (k X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq93 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq59
    | exact resolve eq59 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq27 eq59
    | (have j0 := eq59 (M.op x y) X0
       grind)
    | exact resolve eq59 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq27 eq59
    | (have j0 := eq59 X0 (M.op x y)
       grind)
    | exact resolve eq59 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq119 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq14 (M.op X1 X0) (M.op X0 x)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 (M.op X0 X0) X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 X2)) = X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127 X0 X1 X2
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq127
    | (have j0 := eq127 X0 X1 X2
       grind)
    | exact resolve eq127 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq150 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq122
    | (have j0 := eq122 X0 X1
       grind)
    | exact resolve eq122 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq159 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op (k X0 X0) X1) = X0 ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq150
    | (have j0 := eq150 X0 X1
       grind)
    | exact resolve eq150 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq163 : ∀ X0 X1 : G, (k (k X0 X0) X1) = X1 ∨ (k X0 X0) = X1 ∨ (M.op (k X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq159
    | (have j0 := eq159 X0 X1
       grind)
    | exact resolve eq159 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq172 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq97 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq97
    | exact resolve eq97 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq102 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq102
    | exact resolve eq102 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq224 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X1 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq93
    | exact resolve eq93 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq12
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : (τ (σ x)) = (M.op (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by
    first
    | (have i₁ := eq52 (τ sF4)
       have i₂ := eq71 (τ sF4)
       grind)
    | exact superpose eq71 eq52
    | exact resolve eq52 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | (have i₁ := eq57 sF2
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq57
    | exact resolve eq57 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : (σ x) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq54 sF4
       have i₂ := eq71 sF4
       grind)
    | exact superpose eq71 eq54
    | exact resolve eq54 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq250 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq71 (M.op X0 X0)
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq250 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq250
    | exact resolve eq250 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq258 : (M.op x y) ≠ (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | exact superpose eq248 eq12
    | (have j0 := eq12 (k (M.op x y) (M.op x y)) (τ (σ y))
       grind)
    | exact resolve eq12 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq261 : (M.op x y) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | (have i₁ := eq258
       have i₂ := eq71 (k sF2 sF2)
       grind)
    | exact superpose eq71 eq258
    | exact resolve eq258 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq264 : (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | (have r₁ := eq261
       have r₂ := eq254 (M.op x y)
       grind)
    | exact resolve eq261 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq265 : (k (k (M.op x y) (M.op x y)) (τ (σ y))) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq264
       have i₂ := eq71 (k sF2 sF2)
       grind)
    | exact superpose eq71 eq264
    | exact resolve eq264 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq266 : (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | (have i₁ := eq265
       have i₂ := eq254 sF2
       grind)
    | exact superpose eq254 eq265
    | exact resolve eq265 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq302 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ (τ (σ y)))) := by
    first
    | exact superpose eq266 eq15
    | exact resolve eq15 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq303 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq302
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq302
    | exact resolve eq302 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq304 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq303
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq303
    | exact resolve eq303 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq305 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq27 eq304
    | exact resolve eq304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq308 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq51
    | exact resolve eq51 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) X1) ∨ (M.op X0 X1) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 X1) X0
       have i₂ := eq14 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq51 X0 X0 X2
       have i₂ := eq14 X0 (M.op X2 X0)
       grind)
    | exact superpose eq14 eq51
    | (have j1 := eq14 (M.op X0 X1) X2
       grind)
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (k (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by
    first
    | exact superpose eq247 eq83
    | (have j0 := eq83 (τ (σ x)) (M.op x y)
       grind)
    | (have r₁ := eq83 (τ (σ x)) (M.op x y)
       have r₂ := eq247
       grind)
    | exact resolve eq83 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq247
  have eq446 : (τ (σ x)) = (k (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by grind
  clear eq441
  have eq451 : (σ (τ (σ x))) = (k (σ (k (τ (σ x)) (τ (σ x)))) (σ (M.op x y))) := by
    first
    | exact superpose eq446 eq15
    | exact resolve eq15 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq452 : (σ (τ (σ x))) = (k (σ (k (τ (σ x)) (τ (σ x)))) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq451
    | exact resolve eq451 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq454 : (σ (τ (σ x))) = (k (k (σ (τ (σ x))) (σ (τ (σ x)))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq452
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq452
    | exact resolve eq452 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq455 : (σ x) = (k (k (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq454
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq454
    | exact resolve eq454 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq670 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (k (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq119
    | (have j0 := eq119 (M.op (σ x) (σ y)) X0 x
       grind)
    | exact resolve eq119 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = X0 ∨ (M.op X1 (M.op X0 X2)) = X0 ∨ (M.op X1 (M.op X0 X2)) = (k X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 X2) X0 X1
       have i₂ := eq119 X0 (M.op X1 (M.op X0 X2)) X2
       grind)
    | exact superpose eq119 eq51
    | (have j1 := eq119 (M.op X1 (M.op X0 X2)) X0 X2
       grind)
    | exact resolve eq51 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq688 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (k X0 (M.op X1 (M.op X0 X2))) ∨ (M.op X1 (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq677 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq753 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k X0 X0) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq50 eq148
    | (have j0 := eq148 (M.op (σ x) (σ y)) (M.op (k X0 X0) (σ y)) x
       grind)
    | exact resolve eq148 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq148
  have eq872 : (σ x) = (M.op (k (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq455
       have i₂ := eq163 sF4 sF3
       grind)
    | exact superpose eq163 eq455
    | (have j1 := eq163 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq455 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq305
       have i₂ := eq163 sF3 sF5
       grind)
    | exact superpose eq163 eq305
    | (have j1 := eq163 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq305 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq305
  have eq1329 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq872 eq9
    | exact resolve eq9 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq1362 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) ≠ X0 ∨ (k (k X0 X0) (k X0 X0)) = (k (k X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X0 x
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq82
    | exact resolve eq82 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1396 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (k (k X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1362 X0 X1
       grind)
    | (have r₁ := eq1362 X0 X1
       have r₂ := eq254 X0
       grind)
    | exact resolve eq1362 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1400 : ∀ X0 X1 : G, (k (k X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1396 X0 X1
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq1396
    | exact resolve eq1396 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1780 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq874 eq9
    | exact resolve eq9 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq874 eq51
    | exact resolve eq51 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1835 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1329 sF3
       have i₂ := eq71 sF3
       grind)
    | exact superpose eq71 eq1329
    | exact resolve eq1329 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1780 eq1329
    | exact resolve eq1329 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329 eq1780
  have eq1974 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq33 eq1953
    | exact resolve eq1953 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq1975 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1974
       have r₂ := eq34
       grind)
    | exact resolve eq1974 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq2516 : ∀ X0 X1 : G, (τ X0) = (k (τ (k X0 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq224 (M.op X0 X1) (k X0 X0)
       have i₂ := eq1400 X0 X1
       grind)
    | exact superpose eq1400 eq224
    | exact resolve eq224 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2519 : ∀ X0 X1 : G, (τ X0) = (k (k (τ X0) (τ X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2516 X0 X1
       have i₂ := eq224 X0 X0
       grind)
    | exact superpose eq224 eq2516
    | exact resolve eq2516 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516
  have eq2524 : ∀ X0 : G, (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (M.op (σ (M.op x y)) X0))) := by
    intro X0
    first
    | exact superpose eq37 eq2519
    | exact resolve eq2519 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq3937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq670 eq1783
    | (have j1 := eq670 (σ (M.op x y))
       grind)
    | exact resolve eq1783 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq3965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq3937
  have eq3975 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3965
       have r₂ := eq34
       grind)
    | exact resolve eq3965 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3965
  have eq3994 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3975 eq245
    | exact resolve eq245 eq3975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq3975
  have eq4029 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq753 eq874
    | (have j1 := eq753 (σ (M.op x y))
       grind)
    | exact resolve eq874 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq4067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq4029
  have eq4076 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq4067
       have r₂ := eq34
       grind)
    | exact resolve eq4067 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4067
  have eq4085 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4076 eq172
    | exact resolve eq172 eq4076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq4076
  have eq4536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3994 eq670
    | (have j0 := eq670 (σ (M.op x y))
       grind)
    | exact resolve eq670 eq3994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq3994
  have eq4561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4536
  have eq4564 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq4561
       have r₂ := eq34
       grind)
    | exact resolve eq4561 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq7288 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (M.op x y)) ∨ (τ (σ x)) = (M.op X0 (M.op x y)) ∨ (τ (σ x)) = (k (M.op X0 (M.op x y)) (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 sF2)
       have i₂ := eq326 X0 sF2 (τ sF4)
       grind)
    | exact superpose eq326 eq52
    | (have j1 := eq326 X0 (M.op x y) (τ (σ x))
       grind)
    | exact resolve eq52 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq326
  have eq7352 : ∀ X0 : G, (τ (σ x)) = (k (M.op X0 (M.op x y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq7288 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7288
  have eq7414 : ∀ X0 : G, (σ (τ (σ x))) = (k (σ (M.op X0 (M.op x y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7352 eq15
    | (have j1 := eq7352 X0
       grind)
    | exact resolve eq15 eq7352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7352
  have eq7415 : ∀ X0 : G, (σ x) = (k (σ (M.op X0 (M.op x y))) (σ x)) ∨ (τ (σ x)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7414 X0
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq7414
    | (have j0 := eq7414 X0
       grind)
    | exact resolve eq7414 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7414
  have eq7426 : (σ x) = (k (σ (k (M.op x y) (M.op x y))) (σ x)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7415 (M.op x (k sF2 sF2))
       have i₂ := eq308 sF2 x
       grind)
    | exact superpose eq308 eq7415
    | exact resolve eq7415 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq7415
  have eq7438 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7426
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq7426
    | exact resolve eq7426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7426
  have eq7444 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq7438
    | exact resolve eq7438 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7438
  have eq8341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1975 eq1835
    | exact resolve eq1835 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq8377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8341
  have eq8383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq33 eq8377
    | exact resolve eq8377 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8377
  have eq8385 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq8383
       have r₂ := eq34
       grind)
    | exact resolve eq8383 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8383
  have eq8665 : (σ x) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (σ x)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8385 eq7444
    | exact resolve eq7444 eq8385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7444
  have eq8666 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8385
  have eq8669 : (σ x) = (k (σ x) (σ x)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8665
       have i₂ := eq254 sF4
       grind)
    | exact superpose eq254 eq8665
    | exact resolve eq8665 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8665
  have eq8725 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq8669
       have r₂ := eq8666
       grind)
    | exact resolve eq8669 eq8666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8666 eq8669
  have eq8818 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8725 eq36
    | exact resolve eq36 eq8725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8725
  have eq8830 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8818
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq8818
    | exact resolve eq8818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8818
  have eq8836 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq8830
    | exact resolve eq8830 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8830
  have eq9333 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8836 eq874
    | exact resolve eq874 eq8836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq8836
  have eq9376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9333
  have eq9383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33 eq9376
    | exact resolve eq9376 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9376
  have eq9384 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq9383
       have r₂ := eq34
       grind)
    | exact resolve eq9383 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9383
  have eq9385 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9384 eq33
    | exact resolve eq33 eq9384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9384
  have eq9448 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9385
       have i₂ := eq71 sF4
       grind)
    | exact superpose eq71 eq9385
    | exact resolve eq9385 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9385
  have eq9760 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9448 eq4564
    | exact resolve eq4564 eq9448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4564 eq9448
  have eq9811 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9760
  have eq9843 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq455 eq9811
    | exact resolve eq9811 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq9811
  have eq9844 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9843
  have eq9901 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9844 eq37
    | exact resolve eq37 eq9844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9902 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (M.op x y) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq9844 eq97
    | exact resolve eq97 eq9844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq9939 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  have eq9950 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq9902 x
       have i₂ := eq93 sF5 x
       grind)
    | exact superpose eq93 eq9902
    | exact resolve eq9902 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq9902
  have eq10139 : (M.op x y) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9901 eq43
    | exact resolve eq43 eq9901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10179 : (M.op x y) = (M.op (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10139 eq57
    | exact resolve eq57 eq10139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq10139
  have eq10432 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9901 eq10179
    | exact resolve eq10179 eq9901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9901 eq10179
  have eq10487 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq10432
  have eq10492 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq10487
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq10487
    | exact resolve eq10487 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10487
  have eq10505 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op (σ (M.op x y)) X0))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq10492 eq2524
    | exact resolve eq2524 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524
  have eq10533 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10492 eq15
    | exact resolve eq15 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10492
  have eq10535 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq10533
    | exact resolve eq10533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10533
  have eq10654 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9844 eq10535
    | exact resolve eq10535 eq9844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10535
  have eq10721 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq10654
       have r₂ := eq9939
       grind)
    | exact resolve eq10654 eq9939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10654
  have eq11008 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq10721 eq1400
    | exact resolve eq1400 eq10721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400 eq10721
  have eq14852 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op (σ y) X0))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq9844 eq10505
    | exact resolve eq10505 eq9844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9844 eq10505
  have eq14913 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op (σ y) X0))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq14852 X0
       grind)
    | (have r₁ := eq14852 X0
       have r₂ := eq9939
       grind)
    | exact resolve eq14852 eq9939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14852
  have eq15621 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (M.op (σ y) X0)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq14913 eq15
    | exact resolve eq15 eq14913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14913
  have eq15643 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq15621 X0
       have i₂ := eq36 (M.op sF5 X0)
       grind)
    | exact superpose eq36 eq15621
    | exact resolve eq15621 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15621
  have eq15649 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq27 eq15643
    | (have j0 := eq15643 X0
       grind)
    | exact resolve eq15643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15643
  have eq15753 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq15649 eq688
    | (have j0 := eq688 (σ (M.op x y)) (σ y) X0
       grind)
    | exact resolve eq688 eq15649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq15649
  have eq15774 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq15753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15753
  have eq16125 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15774 eq11008
    | exact resolve eq11008 eq15774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11008 eq15774
  have eq16188 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq16125
  have eq16883 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16188 eq194
    | exact resolve eq194 eq16188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq16188
  have eq17887 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16883 eq9950
    | exact resolve eq9950 eq16883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9950 eq16883
  have eq17902 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq17887
  have eq18108 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq17902 eq36
    | exact resolve eq36 eq17902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17902
  have eq18127 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18108
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq18108
    | exact resolve eq18108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18108
  have eq18134 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq18127
    | exact resolve eq18127 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18127
  have eq18146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18134 eq1835
    | exact resolve eq1835 eq18134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq18202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18146
  have eq18211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33 eq18202
    | exact resolve eq18202 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18202
  have eq18213 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq18211
       have r₂ := eq34
       grind)
    | exact resolve eq18211 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18211
  have eq19364 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18213 eq18134
    | exact resolve eq18134 eq18213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18134
  have eq19368 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18213
  have eq19373 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq19364
       have r₂ := eq19368
       grind)
    | exact resolve eq19364 eq19368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19364 eq19368
  have eq19440 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19373
       have i₂ := eq254 sF4
       grind)
    | exact superpose eq254 eq19373
    | exact resolve eq19373 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq19373
  have eq19463 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq19440
       have r₂ := eq9939
       grind)
    | exact resolve eq19440 eq9939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9939 eq19440
  have eq19728 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq19463 eq37
    | exact resolve eq37 eq19463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq19802 : (M.op x y) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq19728 eq43
    | exact resolve eq43 eq19728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq20146 : (M.op x y) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | exact superpose eq19802 eq64
    | exact resolve eq64 eq19802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq19802
  have eq20230 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq19728 eq20146
    | exact resolve eq20146 eq19728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20146
  have eq20237 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq20230
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq20230
    | exact resolve eq20230 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20230
  have eq20503 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20237 eq15
    | exact resolve eq15 eq20237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20237
  have eq20505 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq20503
    | exact resolve eq20503 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20503
  have eq20515 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq19463 eq20505
    | exact resolve eq20505 eq19463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20505
  have eq20520 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20515 eq249
    | exact resolve eq249 eq20515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq20740 : (σ x) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20520 eq244
    | (have j0 := eq244 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq244 eq20520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq20520
  have eq20801 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq20740
       have r₂ := eq20515
       grind)
    | exact resolve eq20740 eq20515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20740
  have eq20815 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20515 eq20801
    | exact resolve eq20801 eq20515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20801
  have eq20828 : (τ (σ x)) = (k (τ (σ x)) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20815 eq224
    | exact resolve eq224 eq20815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq20815
  have eq20841 : (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq19728 eq20828
    | exact resolve eq20828 eq19728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19728 eq20828
  have eq21421 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20841 eq4085
    | exact resolve eq4085 eq20841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4085 eq20841
  have eq21446 : (σ x) = (σ y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19463 eq21421
    | exact resolve eq21421 eq19463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21421
  have eq21451 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19463 eq21446
    | exact resolve eq21446 eq19463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21446
  have eq21455 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20515 eq21451
    | exact resolve eq21451 eq20515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21451
  have eq21456 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq21455
  have eq23564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21456 eq36
    | exact resolve eq36 eq21456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq21456
  have eq23574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq23564
    | exact resolve eq23564 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23564
  have eq23582 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq23574
       have r₂ := eq34
       grind)
    | exact resolve eq23574 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23574
  have eq23585 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23582 eq33
    | exact resolve eq33 eq23582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq23582
  have eq23707 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq23585
       have i₂ := eq71 sF4
       grind)
    | exact superpose eq71 eq23585
    | exact resolve eq23585 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq23585
  have eq23714 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20515 eq23707
    | exact resolve eq23707 eq20515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20515 eq23707
  have eq24195 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq23714 eq34
    | exact resolve eq34 eq23714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq23714
  have eq24310 : False := by grind
  exact eq24310

/-- `Equation168`: `x = (y ◇ x) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation168 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law168 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law168.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = X0 := by
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
  have eq34 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X0 X2) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X2) (M.op x X0) X3
       have i₂ := eq16 X0 x X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X0) X1 (M.op X0 x)
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq62 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq63 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq66 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq67 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq15
    | exact resolve eq15 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq76 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq70 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq70
    | exact resolve eq70 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70
    | (have j0 := eq70 x
       grind)
    | exact resolve eq70 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq141 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq73 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq73
    | (have j0 := eq73 y
       grind)
    | exact resolve eq73 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq147 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k x y) := by
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
  have eq156 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq147 (M.op X0 X0)
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq147
    | exact resolve eq147 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq63 (M.op sF0 sF0)
       have i₂ := eq147 sF0
       grind)
    | exact superpose eq147 eq63
    | exact resolve eq63 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq163 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq162
    | exact resolve eq162 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq174 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq76 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq76
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq76 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq76
    | (have j0 := eq76 x
       grind)
    | exact resolve eq76 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq193 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq229 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq67 (M.op sF0 sF0)
       have i₂ := eq159 sF0
       grind)
    | exact superpose eq159 eq67
    | exact resolve eq67 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq116 (M.op sF2 sF2)
       have i₂ := eq147 sF2
       grind)
    | exact superpose eq147 eq116
    | exact resolve eq116 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq242 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq231
    | exact resolve eq231 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq267 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq174 (M.op sF1 sF1)
       have i₂ := eq147 sF1
       grind)
    | exact superpose eq147 eq174
    | exact resolve eq174 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq278 : (M.op x y) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq28 eq267
    | exact resolve eq267 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq284 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq193 (M.op sF2 sF2)
       have i₂ := eq159 sF2
       grind)
    | exact superpose eq159 eq193
    | exact resolve eq193 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq193
  have eq633 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 (M.op X1 X0) (M.op X0 X2)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq641 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq712 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq678 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq678
    | (have j0 := eq678 (σ X0)
       grind)
    | exact resolve eq678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq1049 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq638
       grind)
    | exact superpose eq638 eq66
    | exact resolve eq66 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1050 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1049
    | exact resolve eq1049 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1052 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1050
    | exact resolve eq1050 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1052 eq641
    | exact resolve eq641 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1067 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1060
       have r₂ := eq27
       grind)
    | exact resolve eq1060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1075 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq676 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq676
    | (have j0 := eq676 (σ X0) (σ X1)
       grind)
    | exact resolve eq676 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : x = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1067 eq242
    | exact resolve eq242 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq1067
  have eq1153 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1140
    | exact resolve eq1140 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1155 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1153
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1153 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1157 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq638
       have i₂ := eq1155
       grind)
    | exact superpose eq1155 eq638
    | exact resolve eq638 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq1159 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq1155
       grind)
    | exact superpose eq1155 eq66
    | exact resolve eq66 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1162 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1157
  have eq1166 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1159
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1159
    | exact resolve eq1159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1172 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq36
    | exact resolve eq36 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 x
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq16
    | exact resolve eq16 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1189 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1166 eq641
    | exact resolve eq641 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq1166
  have eq1195 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1189
  have eq1206 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1172 eq37
    | exact resolve eq37 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1172 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1231 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1195
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq1195
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq1195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1195 eq40
    | exact resolve eq40 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1195 eq34
    | exact resolve eq34 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1242 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1195 eq16
    | exact resolve eq16 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1195 eq16
    | exact resolve eq16 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1245 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1231
  have eq1248 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1206
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq1206
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq1206 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1234 eq41
    | exact resolve eq41 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1309 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1206 eq1180
    | exact resolve eq1180 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1310 : ∀ X0 : G, x = (k (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = (M.op (M.op X0 x) y) ∨ y = (M.op (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1180 X0
       have i₂ := eq11 (M.op X0 x) y
       grind)
    | exact superpose eq11 eq1180
    | (have j1 := eq11 (M.op X0 x) y
       grind)
    | exact resolve eq1180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1314 : ∀ X0 : G, x = (k (M.op X0 x) y) ∨ x = (M.op X0 x) ∨ y = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 x) y
       have i₂ := eq1180 X0
       grind)
    | exact superpose eq1180 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1319 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1309
  have eq1322 : ∀ X0 : G, x = (k (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq1314 eq1310
    | (have j0 := eq1310 X0
       have j1 := eq1314 X0
       grind)
    | exact resolve eq1310 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310 eq1314
  have eq1323 : ∀ X0 : G, x = (M.op x y) ∨ x = (k (M.op X0 x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1322 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1322
    | (have j0 := eq1322 X0
       grind)
    | exact resolve eq1322 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1324 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq1403 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1258 eq1242
    | exact resolve eq1242 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1413 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1403
  have eq1420 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1413
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq1413
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq1413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1431 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1413 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1431
  have eq1438 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1420
  have eq1441 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1435 eq1438
    | exact resolve eq1438 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq1438
  have eq1842 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq633 X0 X0 X1
       grind)
    | exact superpose eq633 eq16
    | (have j1 := eq633 X0 X0 X1
       grind)
    | exact resolve eq16 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843 : ∀ X0 X1 X2 : G, (k (M.op X2 X0) (M.op X0 X1)) = X0 ∨ (M.op X2 X0) = X0 ∨ (M.op X2 X0) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X2 X0 (M.op X2 X0)
       have i₂ := eq633 X0 X2 X1
       grind)
    | exact superpose eq633 eq34
    | (have j1 := eq633 X0 X2 X1
       grind)
    | exact resolve eq34 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq2002 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1245 eq123
    | exact resolve eq123 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1245
  have eq2019 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq2002
    | exact resolve eq2002 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2049 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq2019 eq1242
    | exact resolve eq1242 eq2019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2060 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq2049
  have eq2067 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq26 eq2060
    | exact resolve eq2060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060
  have eq2068 : y = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2067
  have eq2075 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq2068
       grind)
    | exact superpose eq2068 eq65
    | exact resolve eq65 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2085 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2075
    | exact resolve eq2075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2087 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2085
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2085
    | exact resolve eq2085 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085
  have eq2175 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1441 eq141
    | exact resolve eq141 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1441
  have eq2189 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq2175
    | exact resolve eq2175 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2220 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq2189 eq1242
    | exact resolve eq1242 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242 eq2189
  have eq2231 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by grind
  clear eq2220
  have eq2240 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq2231
    | exact resolve eq2231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2241 : x = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2240
  have eq2248 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66 y
       have i₂ := eq2241
       grind)
    | exact superpose eq2241 eq66
    | exact resolve eq66 eq2241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2241
  have eq2260 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2248
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2248
    | exact resolve eq2248 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248
  have eq2262 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2260
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2260
    | exact resolve eq2260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2702 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1319
       have i₂ := eq1210
       grind)
    | exact superpose eq1210 eq1319
    | exact resolve eq1319 eq1210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq2724 : x = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2702
  have eq2730 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2724 eq67
    | exact resolve eq67 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2724
  have eq2734 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2730
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2730
    | exact resolve eq2730 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2736 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2734
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2734
    | exact resolve eq2734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2734
  have eq2741 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2736 eq649
    | (have j0 := eq649 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq649 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq2745 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1413 eq2741
    | (have j0 := eq2741 X0
       grind)
    | exact resolve eq2741 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq3279 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1248
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq1248
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq1248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3288 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1248 eq35
    | exact resolve eq35 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1248
  have eq3299 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq3279
  have eq3302 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq3299
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq3299 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3299
  have eq3797 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3302 eq65
    | exact resolve eq65 eq3302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3801 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq3302
  have eq3809 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq3797
    | exact resolve eq3797 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797
  have eq3892 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3809 eq676
    | (have j0 := eq676 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq676 (σ (M.op x y)) (σ x)
       have r₂ := eq3809
       grind)
    | exact resolve eq676 eq3809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809
  have eq3893 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq3892
  have eq3898 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1206 eq3893
    | exact resolve eq3893 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq3921 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) y) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq147 (M.op X0 x)
       have i₂ := eq1324 X0
       grind)
    | exact superpose eq1324 eq147
    | (have j1 := eq1324 X0
       grind)
    | exact resolve eq147 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3925 : ∀ X0 X1 : G, (M.op X0 x) = (M.op y (M.op (M.op X0 x) X1)) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 x) (M.op X0 x) X1
       have i₂ := eq1324 X0
       grind)
    | exact superpose eq1324 eq16
    | (have j1 := eq1324 X0
       grind)
    | exact resolve eq16 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3927 : ∀ X0 X1 : G, y = (M.op (M.op X0 x) (M.op y X1)) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 x) (M.op X0 x) x
       have i₂ := eq1324 X0
       grind)
    | exact superpose eq1324 eq34
    | (have j1 := eq1324 X0
       grind)
    | exact resolve eq34 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1324
  have eq4600 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq4635 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1172 eq3927
    | (have j0 := eq3927 X0 x
       grind)
    | exact resolve eq3927 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3927
  have eq4658 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4635
  have eq7087 : ∀ X0 : G, (M.op X0 x) = (M.op y y) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3925 X0 x
       have i₂ := eq4658 X0
       grind)
    | exact superpose eq4658 eq3925
    | (have j0 := eq3925 X0 x
       have j1 := eq4658 X0
       grind)
    | exact resolve eq3925 eq4658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925 eq4658
  have eq7116 : ∀ X0 : G, (M.op X0 x) = (M.op y y) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7087 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7087
  have eq7132 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1319 eq7116
    | (have j0 := eq7116 X0
       grind)
    | exact resolve eq7116 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq7116
  have eq7137 : ∀ X0 : G, x = (k (M.op X0 x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7132 X0
       have j1 := eq4600 X0
       grind)
    | (have r₁ := eq7132 X0
       have r₂ := eq4600 X0
       grind)
    | exact resolve eq7132 eq4600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600 eq7132
  have eq7895 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2745 eq1243
    | exact resolve eq1243 eq2745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq2745
  have eq7924 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq7895
  have eq7938 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq7924 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq7924
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7924
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7924
       grind)
    | exact resolve eq12 eq7924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7924
  have eq7948 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq7938
  have eq7954 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq1413 eq7948
    | exact resolve eq7948 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq7948
  have eq7955 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq7954
  have eq7958 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2736 eq7955
    | exact resolve eq7955 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736 eq7955
  have eq7959 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq7958
  have eq7971 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7959 eq16
    | exact resolve eq16 eq7959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8502 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3898 eq16
    | exact resolve eq16 eq3898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13247 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3898 eq8502
    | exact resolve eq8502 eq3898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898 eq8502
  have eq13306 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq13247
  have eq13319 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1195 eq13306
    | exact resolve eq13306 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13306
  have eq13370 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13319 eq16
    | exact resolve eq16 eq13319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13319
  have eq13902 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13370 eq13370
    | exact resolve eq13370 eq13370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13370
  have eq13945 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq13902
  have eq13958 : (M.op x y) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13945 eq278
    | exact resolve eq278 eq13945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq13945
  have eq14001 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq13958
    | exact resolve eq13958 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13958
  have eq14034 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14001 eq676
    | (have j0 := eq676 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq676 (M.op x y) (M.op x y)
       have r₂ := eq14001
       grind)
    | exact resolve eq676 eq14001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14001
  have eq14035 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq14034
  have eq14036 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq14035
  have eq14058 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14036 eq3288
    | exact resolve eq3288 eq14036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288 eq14036
  have eq14073 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14058
  have eq14085 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq14073
       have r₂ := eq3801
       grind)
    | exact resolve eq14073 eq3801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3801 eq14073
  have eq14093 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14085 eq1206
    | exact resolve eq1206 eq14085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14099 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14085 eq39
    | exact resolve eq39 eq14085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14125 : x = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14085 eq7137
    | exact resolve eq7137 eq14085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7137 eq14085
  have eq14139 : y = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14125
  have eq14169 : y = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14093
  have eq14187 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14169 eq65
    | exact resolve eq65 eq14169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14199 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq14187
    | exact resolve eq14187 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14187
  have eq14201 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14199
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14199
    | exact resolve eq14199 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14199
  have eq14245 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14099 eq42
    | exact resolve eq42 eq14099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14099
  have eq14274 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14169 eq14245
    | exact resolve eq14245 eq14169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14169 eq14245
  have eq14285 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14139 eq65
    | exact resolve eq65 eq14139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14139
  have eq14295 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq14285
    | exact resolve eq14285 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14285
  have eq14297 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14295
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14295
    | exact resolve eq14295 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14295
  have eq14299 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14201 eq14297
    | exact resolve eq14297 eq14201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14201 eq14297
  have eq14479 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14274 eq147
    | exact resolve eq147 eq14274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14274
  have eq14509 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14299 eq181
    | exact resolve eq181 eq14299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq14299
  have eq14531 : y = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31 eq14509
    | exact resolve eq14509 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14509
  have eq14534 : y = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14479 eq14531
    | exact resolve eq14531 eq14479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14479 eq14531
  have eq14535 : y = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14534
  have eq14548 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14535 eq65
    | exact resolve eq65 eq14535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq14535
  have eq14558 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq14548
    | exact resolve eq14548 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14548
  have eq14560 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14558
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14558
    | exact resolve eq14558 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14558
  have eq14575 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq14560 eq648
    | (have j0 := eq648 (σ (M.op x y)) (σ x) x
       grind)
    | exact resolve eq648 eq14560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq14560
  have eq19999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq7959 eq14575
    | exact resolve eq14575 eq7959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7959 eq14575
  have eq20043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq19999
  have eq20065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq26 eq20043
    | exact resolve eq20043 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20043
  have eq20078 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq20065
       have r₂ := eq27
       grind)
    | exact resolve eq20065 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20065
  have eq20254 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20078 eq1842
    | (have j0 := eq1842 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1842 eq20078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842 eq20078
  have eq20255 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq20254
  have eq20285 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2087 eq20255
    | exact resolve eq20255 eq2087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087 eq20255
  have eq20286 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20285
  have eq20321 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20286 eq40
    | exact resolve eq40 eq20286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20286
  have eq20433 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20321 eq7971
    | exact resolve eq7971 eq20321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971 eq20321
  have eq20467 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20433
  have eq20479 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1195 eq20467
    | exact resolve eq20467 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq20467
  have eq20480 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq20479
  have eq20493 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20480 eq40
    | exact resolve eq40 eq20480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20497 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20480 eq156
    | (have r₁ := eq156
       have r₂ := eq20480
       grind)
    | exact resolve eq156 eq20480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq20480
  have eq20502 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq20497
  have eq20506 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := hcon
    have f20506_21 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x y)) ∨ x = y := by
      intro X0
      grind
    have f20506_30 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
    have f20506_35 : (σ (M.op x y)) ≠ (σ y) := by grind
    have f20506_36 : x ≠ (M.op x y) := by grind
    have f20506_37 : (σ x) ≠ (σ (M.op x y)) := by grind
    have f20506_38 : x ≠ y := by grind
    have f20506_40 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x y)) ∨ x = y := by
      intro X0
      first
      | (have j0 := f20506_21 X0
         grind)
      | (have r₁ := f20506_21 X0
         have r₂ := f20506_35
         grind)
      | exact resolve f20506_21 f20506_35
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f20506_42 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (σ (M.op x y)) ∨ x = y := by
      intro X0
      first
      | (have j0 := f20506_40 X0
         grind)
      | (have r₁ := f20506_40 X0
         have r₂ := f20506_36
         grind)
      | exact resolve f20506_40 f20506_36
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f20506_44 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = y := by
      intro X0
      first
      | (have j0 := f20506_42 X0
         grind)
      | (have r₁ := f20506_42 X0
         have r₂ := f20506_37
         grind)
      | exact resolve f20506_42 f20506_37
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f20506_46 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
      intro X0
      first
      | (have j0 := f20506_44 X0
         grind)
      | (have r₁ := f20506_44 X0
         have r₂ := f20506_38
         grind)
      | exact resolve f20506_44 f20506_38
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f20506_54 : (σ x) = (M.op (σ x) (σ x)) := by
      first
      | (have i₁ := f20506_46 (M.op x (σ x))
         have i₂ := f20506_46 x
         grind)
      | exact superpose f20506_46 f20506_46
      | exact resolve f20506_46 f20506_46
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f20506_57 : False := by
      first
      | (have r₁ := f20506_54
         have r₂ := f20506_30
         grind)
      | exact resolve f20506_54 f20506_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f20506_57
  clear eq20493
  have eq20660 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq20506
  have eq20671 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20660 eq284
    | exact resolve eq284 eq20660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20792 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq20671
    | exact resolve eq20671 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20671
  have eq20883 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq676 x x
       have i₂ := eq20792
       grind)
    | exact superpose eq20792 eq676
    | (have j0 := eq676 x x
       grind)
    | (have r₁ := eq676 x x
       have r₂ := eq20792
       grind)
    | exact resolve eq676 eq20792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20792
  have eq20884 : x ≠ x ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq20883
  have eq20885 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq20884
  have eq22640 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20502 eq1052
    | exact resolve eq1052 eq20502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq20502
  have eq22660 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq22640
  have eq22672 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20660 eq22660
    | exact resolve eq22660 eq20660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20660 eq22660
  have eq22677 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20885 eq22672
    | exact resolve eq22672 eq20885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20885 eq22672
  have eq22678 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq22677
  have eq22683 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22678 eq31
    | exact resolve eq31 eq22678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22678
  have eq23001 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq22683
    | exact resolve eq22683 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22683
  have eq23002 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq23001
  have eq23016 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq23002 eq28
    | exact resolve eq28 eq23002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23002
  have eq23230 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq23016
    | exact resolve eq23016 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq23016
  have eq23238 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq23230 eq28
    | exact resolve eq28 eq23230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq23230
  have eq23437 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq23238
    | exact resolve eq23238 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23238
  have eq23438 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq23437
  have eq23443 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23438
       grind)
    | exact superpose eq23438 eq18
    | exact resolve eq18 eq23438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23444 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq23438
       grind)
    | exact superpose eq23438 eq24
    | exact resolve eq24 eq23438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23650 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq23444
    | exact resolve eq23444 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23444
  have eq24917 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq23443 eq42
    | exact resolve eq42 eq23443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq23443
  have eq24968 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq23438 eq24917
    | exact resolve eq24917 eq23438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23438 eq24917
  have eq24975 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq24968 eq229
    | exact resolve eq229 eq24968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq24997 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq24968 eq147
    | exact resolve eq147 eq24968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24968
  have eq25030 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq24975
    | exact resolve eq24975 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24975
  have eq25034 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq23650 eq25030
    | exact resolve eq25030 eq23650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25030
  have eq25039 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq24997 eq712
    | (have j0 := eq712 (M.op x y)
       grind)
    | exact resolve eq712 eq24997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq24997
  have eq25055 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq25039
  have eq25057 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq25055
    | exact resolve eq25055 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25055
  have eq25060 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq23650 eq25057
    | exact resolve eq25057 eq23650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25057
  have eq25075 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq25034 eq2262
    | exact resolve eq2262 eq25034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262 eq25034
  have eq25109 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25075
  have eq25137 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq25060 eq41
    | exact resolve eq41 eq25060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25140 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq25060 eq1239
    | exact resolve eq1239 eq25060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq25060
  have eq25184 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25140
  have eq25197 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq25184
    | exact resolve eq25184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25184
  have eq25202 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25109 eq25197
    | exact resolve eq25197 eq25109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25109 eq25197
  have eq25203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25202
  have eq25206 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25203 eq27
    | exact resolve eq27 eq25203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25218 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq23650 eq25206
    | exact resolve eq25206 eq23650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23650 eq25206
  have eq25224 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25218
  have eq25230 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25203 eq25137
    | exact resolve eq25137 eq25203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25137
  have eq25272 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq25230
  have eq25279 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq25272
    | exact resolve eq25272 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25272
  have eq25282 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq25203 eq25279
    | exact resolve eq25279 eq25203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25279
  have eq25285 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq25282
       have r₂ := eq25224
       grind)
    | exact resolve eq25282 eq25224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25224 eq25282
  have eq29221 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1172 eq1843
    | exact resolve eq1843 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq29579 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op (M.op x y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29221
  have eq29639 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op (M.op x y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25203 eq29579
    | (have j0 := eq29579 X0
       grind)
    | exact resolve eq29579 eq25203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29579
  have eq29689 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39 eq29639
    | (have j0 := eq29639 X0
       grind)
    | exact resolve eq29639 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29639
  have eq29690 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29689
  have eq30421 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1206 eq29690
    | exact resolve eq29690 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq29690
  have eq30461 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30421
  have eq30479 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25203 eq30461
    | exact resolve eq30461 eq25203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25203 eq30461
  have eq30501 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2068
       have i₂ := eq30479
       grind)
    | exact superpose eq30479 eq2068
    | exact resolve eq2068 eq30479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068 eq30479
  have eq30537 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30501
  have eq30555 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25285 eq30537
    | exact resolve eq30537 eq25285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30537
  have eq30556 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30555
  have eq30574 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30556 eq40
    | exact resolve eq40 eq30556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30556
  have eq30607 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30574 eq30574
    | exact resolve eq30574 eq30574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30574
  have eq30770 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq30607
  have eq30788 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30770 eq284
    | exact resolve eq284 eq30770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq30770
  have eq30930 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq30788
    | exact resolve eq30788 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq30788
  have eq31035 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq676 x x
       have i₂ := eq30930
       grind)
    | exact superpose eq30930 eq676
    | (have j0 := eq676 x x
       grind)
    | (have r₁ := eq676 x x
       have r₂ := eq30930
       grind)
    | exact resolve eq676 eq30930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq31036 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq31035
  have eq31037 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq31036
  have eq31091 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq31037
       grind)
    | exact superpose eq31037 eq36
    | exact resolve eq36 eq31037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq31037
  have eq31219 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31091 eq1843
    | exact resolve eq1843 eq31091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31091
  have eq31223 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq31219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31219
  have eq31254 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39 eq31223
    | (have j0 := eq31223 X0
       grind)
    | exact resolve eq31223 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31223
  have eq31255 : ∀ X0 : G, (M.op x y) = (k x (M.op (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31254 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31254
  have eq31897 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq31255
    | exact resolve eq31255 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq31255
  have eq31969 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25285 eq31897
    | exact resolve eq31897 eq25285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25285 eq31897
  have eq31984 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30930
       have i₂ := eq31969
       grind)
    | exact superpose eq31969 eq30930
    | exact resolve eq30930 eq31969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30930 eq31969
  have eq32018 : x = (M.op x y) := by grind
  clear eq31984
  have eq32035 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq32018
       grind)
    | exact superpose eq32018 eq18
    | exact resolve eq18 eq32018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq32036 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq32018
       grind)
    | exact superpose eq32018 eq22
    | exact resolve eq22 eq32018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq32039 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq32018
       grind)
    | exact superpose eq32018 eq61
    | exact resolve eq61 eq32018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq32042 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq153
       have i₂ := eq32018
       grind)
    | exact superpose eq32018 eq153
    | (have r₁ := eq153
       have r₂ := eq32018
       grind)
    | exact resolve eq153 eq32018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq32052 : y = (k (M.op x y) y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq32042
  have eq32055 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32036 eq20
    | exact resolve eq20 eq32036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32310 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq32035 eq39
    | exact resolve eq39 eq32035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq32035
  have eq32344 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq32310
       have i₂ := eq32018
       grind)
    | exact superpose eq32018 eq32310
    | exact resolve eq32310 eq32018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32018 eq32310
  have eq32349 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq32344 eq163
    | exact resolve eq163 eq32344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq32382 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32344 eq147
    | exact resolve eq147 eq32344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq32405 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq32349
    | exact resolve eq32349 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32349
  have eq32409 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq32055 eq32405
    | exact resolve eq32405 eq32055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32405
  have eq32421 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq32382 eq1075
    | (have j0 := eq1075 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1075 eq32382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq32382
  have eq32433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq32421
  have eq32434 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq32433
  have eq32439 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq32434
    | exact resolve eq32434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32434
  have eq32444 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32055 eq32439
    | exact resolve eq32439 eq32055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32439
  have eq32539 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32444 eq40
    | exact resolve eq40 eq32444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq32444
  have eq32648 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq32539 eq1843
    | exact resolve eq1843 eq32539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq32655 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq45 eq32648
    | (have j0 := eq32648 X0
       grind)
    | exact resolve eq32648 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq32648
  have eq32656 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq32655 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32655
  have eq34807 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32052 eq32039
    | exact resolve eq32039 eq32052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32039 eq32052
  have eq34828 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq34807
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34807
    | exact resolve eq34807 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34807
  have eq34832 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32344 eq34828
    | exact resolve eq34828 eq32344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32344 eq34828
  have eq35025 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41 eq32656
    | exact resolve eq32656 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq32656
  have eq35081 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35025 eq34832
    | exact resolve eq34832 eq35025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34832
  have eq35166 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35081 eq32539
    | exact resolve eq32539 eq35081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32539 eq35081
  have eq35192 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq35166
    | exact resolve eq35166 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq35166
  have eq35193 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq35192
  have eq35205 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35193 eq27
    | exact resolve eq27 eq35193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35193
  have eq35222 : y = (M.op x y) := by
    first
    | (have r₁ := eq35205
       have r₂ := eq32055
       grind)
    | exact resolve eq35205 eq32055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35205
  have eq35224 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq35222
       grind)
    | exact superpose eq35222 eq24
    | exact resolve eq24 eq35222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35222
  have eq35359 : (σ x) = (σ y) := by
    first
    | exact superpose eq32036 eq35224
    | exact resolve eq35224 eq32036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32036 eq35224
  have eq35537 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35359 eq35025
    | exact resolve eq35025 eq35359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35025 eq35359
  have eq35569 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32409 eq35537
    | exact resolve eq35537 eq32409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32409 eq35537
  have eq35570 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35569
  have eq35629 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq35570 eq27
    | exact resolve eq27 eq35570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq35570
  have eq35648 : False := by grind
  exact eq35648

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq19
  have eq35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq96 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq105 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq279 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105 x y
       grind)
    | exact superpose eq105 eq16
    | (have j1 := eq105 x y
       grind)
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq2166 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq279
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq279
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq279
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq279
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq279 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq2167 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq2166
  have eq7651 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq7704 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq96 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq7726 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7651 X0
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq7651
    | (have j0 := eq7651 X0
       grind)
    | exact resolve eq7651 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq7651
  have eq7734 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7726 X0
       have j1 := eq7704 X0
       grind)
    | (have r₁ := eq7726 X0
       have r₂ := eq7704 X0
       grind)
    | exact resolve eq7726 eq7704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7704 eq7726
  have eq7741 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7734 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7734
    | exact resolve eq7734 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7734
  have eq7843 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq7741 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq7741
    | exact resolve eq7741 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq7741
  have eq7851 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7843 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7843
    | exact resolve eq7843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7843
  have eq8208 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7851 (σ X0)
       grind)
    | exact superpose eq7851 eq15
    | exact resolve eq15 eq7851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8228 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8208 X0
       have i₂ := eq7851 X0
       grind)
    | exact superpose eq7851 eq8208
    | exact resolve eq8208 eq7851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7851 eq8208
  have eq9186 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq149 (σ X0)
       have i₂ := eq8228 X0
       grind)
    | exact superpose eq8228 eq149
    | exact resolve eq149 eq8228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26018 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2167
       grind)
    | exact superpose eq2167 eq16
    | exact resolve eq16 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq26019 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26018
       have r₂ := eq8228 x
       grind)
    | exact resolve eq26018 eq8228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26018
  have eq26020 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26019
       have i₂ := eq8228 y
       grind)
    | exact superpose eq8228 eq26019
    | exact resolve eq26019 eq8228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26019
  have eq26022 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26020
       grind)
    | exact superpose eq26020 eq10
    | exact resolve eq10 eq26020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26020
  have eq26126 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26022
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26022
    | exact resolve eq26022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26022
  have eq26147 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26126
       grind)
    | exact superpose eq26126 eq16
    | exact resolve eq16 eq26126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26126
  have eq26148 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26147
       have r₂ := eq8228 x
       grind)
    | exact resolve eq26147 eq8228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8228 eq26147
  have eq26449 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq26148
       grind)
    | exact superpose eq26148 eq10
    | exact resolve eq10 eq26148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26148
  have eq26553 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26449
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26449
    | exact resolve eq26449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26449
  have eq26554 : x = (M.op y y) := by grind
  clear eq26553
  have eq26572 : y = (M.op x y) := by
    first
    | (have i₁ := eq149 y
       have i₂ := eq26554
       grind)
    | exact superpose eq26554 eq149
    | exact resolve eq149 eq26554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq26584 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9186 y
       have i₂ := eq26554
       grind)
    | exact superpose eq26554 eq9186
    | exact resolve eq9186 eq26554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9186 eq26554
  have eq28167 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26584
       grind)
    | exact superpose eq26584 eq16
    | exact resolve eq16 eq26584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26584
  have eq28242 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq28167
       have i₂ := eq26572
       grind)
    | exact superpose eq26572 eq28167
    | exact resolve eq28167 eq26572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26572 eq28167
  have eq28243 : False := by grind
  exact eq28243

/-- `Equation3740`: `x ◇ y = (x ◇ z) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pyx_Equation3740 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3740 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3740.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X2 X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq28 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 (M.op X2 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq9 X1 X1 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 (M.op X1 X0)
       have i₂ := eq9 X1 X0 X0
       grind)
    | exact superpose eq9 eq58
    | exact resolve eq58 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k (M.op X0 X0) X1) (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 X0)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq60
    | (have j1 := eq17 X0 X1
       grind)
    | exact resolve eq60 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X2 X1) = (k X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq17 X1 X2
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq17 X0 X1
       grind)
    | exact resolve eq12 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq75 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq72 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq67
    | (have j0 := eq67 X1 (σ X0)
       grind)
    | exact resolve eq67 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq75 X0 (σ y) (σ x)
       grind)
    | exact superpose eq75 eq16
    | (have j1 := eq75 X0 X0 (σ y)
       grind)
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq95 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq98 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (k (k X0 X0) X1) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq58
    | exact resolve eq58 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq101 : ∀ X0 X1 : G, (M.op X1 X0) = (k (k X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq60
    | exact resolve eq60 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq102 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k (k X0 X0) X1) (M.op (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq62
    | exact resolve eq62 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq110 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq87
    | (have j0 := eq87 X0
       grind)
    | exact resolve eq87 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq113 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq98
    | (have j0 := eq98 X0 X0
       grind)
    | exact resolve eq98 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (M.op X0 X0)
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq96
    | exact resolve eq96 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq114
    | exact resolve eq114 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq120 : ∀ X0 X1 : G, (k (σ (k X0 X0)) X1) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (σ X1) X1
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq100
    | exact resolve eq100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (k (τ (k X0 X0)) X1) = (M.op X1 (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (τ X0) X1
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq100
    | exact resolve eq100 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k (σ (k X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq101
    | exact resolve eq101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq134 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq116
    | exact resolve eq116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (k X0 X0)) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (τ X0) X1
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq116
    | exact resolve eq116 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op (k X0 X0) (k X2 X0)) ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 X2 X1
       have i₂ := eq75 X0 X1 X2
       grind)
    | exact superpose eq75 eq116
    | (have j1 := eq75 X0 X1 X2
       grind)
    | exact resolve eq116 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq140 : ∀ X0 X1 : G, (k (k X0 X0) X1) = (M.op (k X1 X1) (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X1 (k X0 X0)
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq116
    | exact resolve eq116 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (M.op X2 (σ X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 X1 X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq120
    | (have j1 := eq67 (σ X1) X2
       grind)
    | exact resolve eq120 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k (σ (k X0 X0)) X1) (M.op (σ (k X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (σ (k X0 X0))
       have i₂ := eq120 X0 X1
       grind)
    | exact superpose eq120 eq9
    | exact resolve eq9 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 X2 : G, (k (τ X1) X2) = (M.op X2 (τ X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X1 X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq121
    | (have j1 := eq67 (τ X1) X2
       grind)
    | exact resolve eq121 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X1 X1) ∨ (k X0 X0) = X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 (k X1 X1)
       have i₂ := eq118 X1
       grind)
    | exact superpose eq118 eq113
    | (have j0 := eq113 X0 X0
       grind)
    | (have r₁ := eq113 X0 (k X0 X0)
       have r₂ := eq118 X0
       grind)
    | exact resolve eq113 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq187 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq191 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 (σ (k X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 (σ X1)
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq187
    | (have j0 := eq187 X0 X1
       grind)
    | exact resolve eq187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 (τ (k X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 (τ X1)
       have i₂ := eq30 X1 X1
       grind)
    | exact superpose eq30 eq187
    | (have j0 := eq187 X0 X1
       grind)
    | exact resolve eq187 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (k X1 X1))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (k X1 X1)
       have i₂ := eq187 (τ X0) X1
       grind)
    | exact superpose eq187 eq18
    | (have j1 := eq187 (τ X0) X1
       grind)
    | exact resolve eq18 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq198 : ∀ X0 X1 : G, (k X0 (σ (k X1 X1))) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq201 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 (σ (k X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq206 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 X1))) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq191 X0 X1
       grind)
    | exact superpose eq191 eq100
    | (have j1 := eq191 X0 X1
       grind)
    | exact resolve eq100 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 : G, (k X0 (τ (k X1 X1))) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq192 X0 X1
       grind)
    | exact superpose eq192 eq100
    | (have j1 := eq192 X0 X1
       grind)
    | exact resolve eq100 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (k (σ X1) (M.op X2 (σ X1))) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X1 X2
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq126
    | (have j1 := eq67 X0 X1
       grind)
    | exact resolve eq126 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq126
  have eq343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) X2) = (M.op (k (k X0 X0) X1) (M.op (M.op X3 (k X0 X0)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 (k X0 X0) X3 X2
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq54
    | exact resolve eq54 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ (k X0 X0))) X3) = (M.op (M.op X2 (M.op (σ X0) X1)) (M.op (M.op (σ X0) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X2 (M.op (σ X0) X1) (σ (k X0 X0)) X3
       have i₂ := eq134 X0 X1
       grind)
    | exact superpose eq134 eq54
    | exact resolve eq54 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq349 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (τ (k X0 X0))) X3) = (M.op (M.op X2 (M.op (τ X0) X1)) (M.op (M.op (τ X0) X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X2 (M.op (τ X0) X1) (τ (k X0 X0)) X3
       have i₂ := eq135 X0 X1
       grind)
    | exact superpose eq135 eq54
    | exact resolve eq54 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq350 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (k X0 X0)) X3) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X2 (M.op X0 X1) (k X0 X0) X3
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq54
    | exact resolve eq54 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X0 X2)) = (M.op (M.op X3 X0) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X3 X0 X1 (M.op X0 X2)
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 (M.op (M.op X0 X1) X1)
       have i₂ := eq54 (M.op X0 X1) X1 X0 X1
       grind)
    | exact superpose eq54 eq96
    | exact resolve eq96 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq373 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X2 (k X0 X0)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq350 X0 x X2 X3
       have i₂ := eq9 X2 X3 (M.op X0 x)
       grind)
    | exact superpose eq9 eq350
    | exact resolve eq350 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq374 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X2 (τ (k X0 X0))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq349 X0 x X2 X3
       have i₂ := eq9 X2 X3 (M.op (τ X0) x)
       grind)
    | exact superpose eq9 eq349
    | exact resolve eq349 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq375 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X2 (σ (k X0 X0))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq348 X0 x X2 X3
       have i₂ := eq9 X2 X3 (M.op (σ X0) x)
       grind)
    | exact superpose eq9 eq348
    | exact resolve eq348 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq378 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) X2) = (M.op (k (k X0 X0) X1) (M.op (k (k X0 X0) X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq343 X0 X1 X2 X3
       have i₂ := eq100 X0 X3
       grind)
    | exact superpose eq100 eq343
    | exact resolve eq343 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq386 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (k (k X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq373 X0 X2 X3
       have i₂ := eq100 X0 X2
       grind)
    | exact superpose eq100 eq373
    | exact resolve eq373 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq387 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (k (τ (k X0 X0)) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq374 X0 X2 X3
       have i₂ := eq121 X0 X2
       grind)
    | exact superpose eq121 eq374
    | exact resolve eq374 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq374
  have eq388 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op (k (σ (k X0 X0)) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq375 X0 X2 X3
       have i₂ := eq120 X0 X2
       grind)
    | exact superpose eq120 eq375
    | exact resolve eq375 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq375
  have eq390 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) X2) = (M.op (k (k X0 X0) X1) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq378 X0 X1 X2 X3
       have i₂ := eq386 X0 X3 X2
       grind)
    | exact superpose eq386 eq378
    | exact resolve eq378 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq391 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X0 X1 X2
       have i₂ := eq386 X0 X1 (M.op (k X0 X0) X2)
       grind)
    | exact superpose eq386 eq102
    | exact resolve eq102 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq395 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (σ (k X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 X0 X1 X2
       have i₂ := eq388 X0 X1 (M.op (σ (k X0 X0)) X2)
       grind)
    | exact superpose eq388 eq171
    | exact resolve eq171 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq388
  have eq396 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X3) X2) = (M.op X1 (M.op X3 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq390 x X1 X2 X3
       have i₂ := eq386 x X1 (M.op X3 X2)
       grind)
    | (have i₁ := eq390 x X1 X2 X3
       have i₂ := eq386 x (k (k x x) X1) (M.op X3 X2)
       grind)
    | exact superpose eq386 eq390
    | exact resolve eq390 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq399 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op X0 (M.op X1 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq396 X0 X0 X1
       grind)
    | exact superpose eq396 eq360
    | exact resolve eq360 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq415 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq396 X0 (M.op X2 X1) X2
       grind)
    | exact superpose eq396 eq9
    | exact resolve eq9 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X2)) = (M.op X3 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq353 X0 X1 X2 X3
       have i₂ := eq396 X3 (M.op X0 X2) X1
       grind)
    | exact superpose eq396 eq353
    | exact resolve eq353 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq426 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq416 X1 X0 X2 X3
       have i₂ := eq396 X3 (M.op X0 X2) X1
       grind)
    | exact superpose eq396 eq416
    | exact resolve eq416 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq439 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op X0 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1
       have i₂ := eq396 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq396 eq399
    | exact resolve eq399 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq447 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq396 X1 X1 X0
       grind)
    | exact superpose eq396 eq439
    | exact resolve eq439 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq453 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq447 X1 x
       have i₂ := eq396 X1 x x
       grind)
    | exact superpose eq396 eq447
    | exact resolve eq447 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq457 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 (k X1 X1)) (M.op X0 (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq453
    | exact resolve eq453 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq460 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (k (k X1 X1) X0) (k (k X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X1 X0
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq457
    | exact resolve eq457 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq462 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq415 X1 X0 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq415
    | exact resolve eq415 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 (M.op X0 X1)
       have i₂ := eq415 (k X0 X0) X1 X0
       grind)
    | exact superpose eq415 eq116
    | exact resolve eq116 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq415
  have eq510 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (k X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 X1
       have i₂ := eq100 X0 X0
       grind)
    | exact superpose eq100 eq462
    | exact resolve eq462 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq582 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 (M.op X0 X1) X1
       have i₂ := eq96 (M.op X0 X1)
       grind)
    | exact superpose eq96 eq396
    | exact resolve eq396 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 X2 : G, (k (k X0 X0) (M.op X1 X2)) = (M.op X1 (M.op X2 (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 X1 (k X0 X0) X2
       have i₂ := eq100 X0 (M.op X1 X2)
       grind)
    | exact superpose eq100 eq396
    | exact resolve eq396 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 : G, (k (k X0 X0) (M.op X1 X2)) = (M.op X1 (k (k X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq587 X0 X1 X2
       have i₂ := eq100 X0 X2
       grind)
    | exact superpose eq100 eq587
    | exact resolve eq587 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq598 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (k (k (k X1 X1) X0) (k (k X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq460 X0 X1
       have i₂ := eq582 X0 X1
       grind)
    | exact superpose eq582 eq460
    | exact resolve eq460 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460 eq582
  have eq635 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X0)) ∨ (k X0 (τ (k X1 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq510 X0 X2
       have i₂ := eq192 X0 X1
       grind)
    | exact superpose eq192 eq510
    | (have j1 := eq192 X0 X1
       grind)
    | exact resolve eq510 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq636 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (k X0 X0)) ∨ (k X0 (σ (k X1 X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq510 X0 X2
       have i₂ := eq191 X0 X1
       grind)
    | exact superpose eq191 eq510
    | (have j1 := eq191 X0 X1
       grind)
    | exact resolve eq510 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq664 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 X1))) = X0 ∨ (M.op X2 X0) = (k (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq636 X0 X1 X2
       have i₂ := eq100 X0 X2
       grind)
    | exact superpose eq100 eq636
    | (have j0 := eq636 X0 X1 X2
       grind)
    | exact resolve eq636 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq665 : ∀ X0 X1 X2 : G, (k X0 (τ (k X1 X1))) = X0 ∨ (M.op X2 X0) = (k (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq635 X0 X1 X2
       have i₂ := eq100 X0 X2
       grind)
    | exact superpose eq100 eq635
    | (have j0 := eq635 X0 X1 X2
       grind)
    | exact resolve eq635 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq685 : ∀ X0 X1 : G, (M.op X0 (k (k X1 X1) X0)) = (k (k (k X1 X1) X0) (k (k X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 (k (k X1 X1) X0)
       have i₂ := eq386 X1 X0 (k (k X1 X1) X0)
       grind)
    | exact superpose eq386 eq96
    | exact resolve eq96 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op X0 (k (k X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq598 X0 X1
       have i₂ := eq685 X0 X1
       grind)
    | exact superpose eq685 eq598
    | exact resolve eq598 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq685
  have eq717 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq485 X0 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq485
    | exact resolve eq485 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 : G, (M.op X1 (k (k X0 X0) X1)) = (M.op (k X1 X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X1 (k X0 X0)
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq485
    | exact resolve eq485 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 : G, (M.op X1 (k (k X0 X0) X1)) = (k (k X0 X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 X1
       have i₂ := eq100 X0 (k X1 X1)
       grind)
    | exact superpose eq100 eq728
    | exact resolve eq728 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq745 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq717 X0
       have i₂ := eq100 X0 X0
       grind)
    | exact superpose eq100 eq717
    | exact resolve eq717 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq750 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (k (k X1 X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq738 X1 X0
       grind)
    | exact superpose eq738 eq701
    | exact resolve eq701 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq738
  have eq763 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq745 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq745
    | exact resolve eq745 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq745 (τ X0)
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq745
    | exact resolve eq745 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 : G, (τ (k (k X0 X0) X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq764 X0
       have i₂ := eq30 X0 (k X0 X0)
       grind)
    | exact superpose eq30 eq764
    | exact resolve eq764 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq776 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq763 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq763
    | exact resolve eq763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq859 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = (M.op (τ (k (k X1 X1) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq387 X1 (τ X0) X2
       have i₂ := eq30 X0 (k X1 X1)
       grind)
    | exact superpose eq30 eq387
    | exact resolve eq387 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq2722 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X0 X1) X1))) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq426 X0 (M.op X0 X1) X1 X2
       have i₂ := eq96 (M.op X0 X1)
       grind)
    | exact superpose eq96 eq426
    | exact resolve eq426 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq2963 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X0 X1) X1))) = (k (k (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2722 X0 X1 X2
       have i₂ := eq100 (M.op X0 X1) X2
       grind)
    | exact superpose eq100 eq2722
    | exact resolve eq2722 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722
  have eq3009 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X0 X1) X1))) = (k (k (k X1 X1) (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2963 X0 X1 X2
       have i₂ := eq750 X0 X1
       grind)
    | exact superpose eq750 eq2963
    | exact resolve eq2963 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq3021 : ∀ X0 X1 X2 : G, (k (k (k X1 X1) (k X0 X0)) X2) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3009 X0 X1 X2
       have i₂ := eq396 X0 X1 X1
       grind)
    | exact superpose eq396 eq3009
    | exact resolve eq3009 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009
  have eq3032 : ∀ X0 X1 X2 : G, (k (k (k X1 X1) (k X0 X0)) X2) = (M.op X2 (M.op (k X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3021 X0 X1 X2
       have i₂ := eq485 X0 (M.op X1 X1)
       grind)
    | exact superpose eq485 eq3021
    | exact resolve eq3021 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq3039 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (k (k (k X1 X1) (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3032 X0 X1 X2
       have i₂ := eq391 X0 X2 (M.op X1 X1)
       grind)
    | exact superpose eq391 eq3032
    | exact resolve eq3032 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3032
  have eq3044 : ∀ X0 X1 X2 : G, (M.op X2 (k X1 X1)) = (k (k (k X1 X1) (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3039 X0 X1 X2
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq3039
    | exact resolve eq3039 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039
  have eq3049 : ∀ X0 X1 X2 : G, (k (k X1 X1) X2) = (k (k (k X1 X1) (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3044 X0 X1 X2
       have i₂ := eq100 X1 X2
       grind)
    | exact superpose eq100 eq3044
    | exact resolve eq3044 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq3044
  have eq3810 : ∀ X0 X1 : G, (τ (k (k (k X1 X1) (k X0 X0)) (M.op X0 X1))) = (M.op (τ (k (k X1 X1) (k X0 X0))) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq775 (M.op X0 X1)
       have i₂ := eq750 X0 X1
       grind)
    | exact superpose eq750 eq775
    | exact resolve eq775 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq775
  have eq3829 : ∀ X0 X1 : G, (τ (k (k (k X1 X1) (k X0 X0)) (M.op X0 X1))) = (M.op (τ (k X0 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3810 X0 X1
       have i₂ := eq859 (k X0 X0) X1 (τ (M.op X0 X1))
       grind)
    | exact superpose eq859 eq3810
    | exact resolve eq3810 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq3810
  have eq3886 : ∀ X0 X1 : G, (M.op (τ (k X0 X0)) (τ (M.op X0 X1))) = (τ (k (k X1 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3829 X0 X1
       have i₂ := eq3049 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq3049 eq3829
    | exact resolve eq3829 eq3049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829
  have eq3932 : ∀ X0 X1 : G, (M.op (τ (k X0 X0)) (τ (M.op X0 X1))) = (τ (M.op X0 (k (k X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3886 X0 X1
       have i₂ := eq594 X1 X0 X1
       grind)
    | exact superpose eq594 eq3886
    | exact resolve eq3886 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq3886
  have eq3954 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (k X0 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3932 X0 X1
       have i₂ := eq510 X1 X0
       grind)
    | exact superpose eq510 eq3932
    | exact resolve eq3932 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq3932
  have eq4060 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op (τ (σ (k X0 X0))) (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3954 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3954
    | exact resolve eq3954 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3954
  have eq4106 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op (k X0 X0) (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4060 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq4060
    | exact resolve eq4060 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq5605 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X0))) ∨ (σ X0) = (k (σ X0) (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq201
    | (have j0 := eq201 (σ X0) X1
       grind)
    | exact resolve eq201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq5635 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5605 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq5605
    | (have j0 := eq5605 X0 X1
       grind)
    | exact resolve eq5605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5605
  have eq5639 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (k (σ X0) (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5635 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5635
    | (have j0 := eq5635 X0 X1
       grind)
    | exact resolve eq5635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq5640 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (k X1 X1))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5639 X0 X1
       have i₂ := eq15 X0 (k X1 X1)
       grind)
    | exact superpose eq15 eq5639
    | (have j0 := eq5639 X0 X1
       grind)
    | exact resolve eq5639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5639
  have eq5646 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (k X1 X1)))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5640 X0 (τ X1)
       have i₂ := eq30 X1 X1
       grind)
    | exact superpose eq30 eq5640
    | (have j0 := eq5640 X0 X1
       grind)
    | exact resolve eq5640 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5640
  have eq5689 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (k X1 X1)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5646 X0 X1
       have i₂ := eq19 (k X1 X1) X0
       grind)
    | exact superpose eq19 eq5646
    | (have j0 := eq5646 X0 X1
       grind)
    | exact resolve eq5646 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5646
  have eq5692 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5689 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5689
    | (have j0 := eq5689 (τ X0) X1
       grind)
    | exact resolve eq5689 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5701 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (τ (k X1 X1))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5689 X0 (τ X1)
       have i₂ := eq30 X1 X1
       grind)
    | exact superpose eq30 eq5689
    | (have j0 := eq5689 X0 X1
       grind)
    | exact resolve eq5689 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5689
  have eq5722 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5692 X0 X1
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq5692
    | (have j0 := eq5692 X0 X1
       grind)
    | exact resolve eq5692 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5692
  have eq5743 : ∀ X0 X1 X2 : G, (k (k X0 X0) (σ X2)) = (σ (k (τ X0) X2)) ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (k X0 X0) X2
       have i₂ := eq5722 X0 X1
       grind)
    | exact superpose eq5722 eq18
    | (have j1 := eq5722 X0 X1
       grind)
    | exact resolve eq18 eq5722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5722
  have eq5750 : ∀ X0 X1 X2 : G, (k (k X0 X0) (σ X2)) = (k X0 (σ X2)) ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5743 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq5743
    | (have j0 := eq5743 X0 X1 X2
       grind)
    | exact resolve eq5743 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5743
  have eq6413 : ∀ X0 X1 X2 : G, (k X2 (σ (τ (k X0 X0)))) = X2 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X2 (τ X0) X1
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq206
    | (have j0 := eq206 X2 X1 X1
       grind)
    | exact resolve eq206 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq6442 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6413 X0 X1 X2
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq6413
    | (have j0 := eq6413 X0 X1 X2
       grind)
    | exact resolve eq6413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6413
  have eq6449 : ∀ X0 X1 X2 X3 : G, (k X2 (k X3 X3)) = X2 ∨ (M.op X0 X2) = (k X2 (k (k X1 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6442 X3 (k (k X1 X1) X0) X2
       have i₂ := eq386 X1 X0 X2
       grind)
    | exact superpose eq386 eq6442
    | (have j0 := eq6442 X3 X1 X2
       grind)
    | exact resolve eq6442 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6474 : ∀ X0 X1 : G, (σ (k (k X0 X0) X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (k (σ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6442 X1 (σ (k X0 X0)) (σ X0)
       have i₂ := eq776 X0
       grind)
    | exact superpose eq776 eq6442
    | (have j0 := eq6442 X1 X1 (σ X0)
       grind)
    | exact resolve eq6442 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq6514 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq6442 X0 (σ x) (σ y)
       grind)
    | exact superpose eq6442 eq16
    | (have j1 := eq6442 X0 x (σ y)
       grind)
    | exact resolve eq16 eq6442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6442
  have eq6520 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6514 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6514
    | (have j0 := eq6514 X0
       grind)
    | exact resolve eq6514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514
  have eq6526 : ∀ X0 X1 : G, (σ (k (k X0 X0) X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (k (σ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6474 X0 X1
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq6474
    | (have j0 := eq6474 X0 X1
       grind)
    | exact resolve eq6474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6474
  have eq6546 : ∀ X0 X1 X2 : G, (σ X1) = (k (σ X1) (k X2 X2)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (k X2 X2) X1
       have i₂ := eq224 X1 X2 X0
       grind)
    | exact superpose eq224 eq19
    | (have j1 := eq224 X1 X1 X0
       grind)
    | exact resolve eq19 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq6571 : ∀ X0 : G, (σ (k y x)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) (k X0 X0)) := by
    intro X0
    first
    | exact superpose eq6546 eq6520
    | (have j0 := eq6520 X0
       have j1 := eq6546 X0 y X0
       grind)
    | exact resolve eq6520 eq6546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6520 eq6546
  have eq6572 : ∀ X0 : G, (σ y) = (k (σ y) (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6571
  have eq6590 : ∀ X0 : G, (k y (τ (k X0 X0))) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 (k X0 X0) y
       have i₂ := eq6572 X0
       grind)
    | exact superpose eq6572 eq28
    | exact resolve eq28 eq6572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6572
  have eq6591 : ∀ X0 : G, y = (k y (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6590 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6590
    | exact resolve eq6590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590
  have eq6602 : ∀ X0 : G, y = (k y (τ (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6591 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6591
    | exact resolve eq6591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6591
  have eq6614 : ∀ X0 : G, y = (k y (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6602 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq6602
    | exact resolve eq6602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6602
  have eq14264 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (k X1 X1)))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (τ (k X1 X1)) X0
       have i₂ := eq5701 X0 X1
       grind)
    | exact superpose eq5701 eq28
    | (have j1 := eq5701 X0 X1
       grind)
    | exact resolve eq28 eq5701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5701
  have eq14275 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 (τ (τ (k X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14264 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14264
    | (have j0 := eq14264 X0 X1
       grind)
    | exact resolve eq14264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14264
  have eq14291 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (τ (τ (k X1 X1)))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14275 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq14275
    | (have j0 := eq14275 (σ X0) X1
       grind)
    | exact resolve eq14275 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14275
  have eq19194 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x (σ y)
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x x
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq19243 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq19194
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19194
    | exact resolve eq19194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19194
  have eq19541 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq165 X0 y (σ x)
       grind)
    | exact superpose eq165 eq16
    | (have j1 := eq165 X0 y x
       grind)
    | exact resolve eq16 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq19564 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq19541 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19541
    | (have j0 := eq19541 X0
       grind)
    | exact resolve eq19541 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19541
  have eq25867 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (k X2 (σ X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq174
    | (have j0 := eq174 X2 (σ X0) X2
       grind)
    | exact resolve eq174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq25974 : ∀ X0 : G, (σ (k y x)) ≠ (σ (k y x)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq25867 eq110
    | (have j0 := eq110 X0
       have j1 := eq25867 y x X0
       grind)
    | exact resolve eq110 eq25867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq25867
  have eq25980 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq25974 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25974
  have eq26025 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (k X0 (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq396 (σ y) X1 X0
       have i₂ := eq25980 X0
       grind)
    | exact superpose eq25980 eq396
    | exact resolve eq396 eq25980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq26069 : ∀ X0 X1 : G, (M.op (k X0 (σ y)) X1) = (k (M.op X0 X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq26025 X0 X1
       have i₂ := eq25980 (M.op X0 X1)
       grind)
    | exact superpose eq25980 eq26025
    | exact resolve eq26025 eq25980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26025
  have eq26427 : ∀ X0 X1 : G, (M.op (k X0 (σ y)) (M.op X0 X1)) = (k (M.op (k X0 X0) X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq26069 X0 (M.op X0 X1)
       have i₂ := eq485 X0 X1
       grind)
    | exact superpose eq485 eq26069
    | exact resolve eq26069 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26494 : ∀ X0 X1 : G, (k (τ (M.op X0 X1)) y) = (τ (M.op (k X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X0 X1) y
       have i₂ := eq26069 X0 X1
       grind)
    | exact superpose eq26069 eq23
    | exact resolve eq23 eq26069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26553 : ∀ X0 X1 : G, (M.op (k X0 (σ y)) (M.op X0 X1)) = (M.op (k (k X0 X0) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26427 X0 X1
       have i₂ := eq26069 (k X0 X0) X1
       grind)
    | exact superpose eq26069 eq26427
    | exact resolve eq26427 eq26069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26069 eq26427
  have eq26601 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (k X0 (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26553 X0 X1
       have i₂ := eq386 X0 (σ y) X1
       grind)
    | (have i₁ := eq26553 X0 x
       have i₂ := eq386 X0 (k (k X0 X0) (σ y)) x
       grind)
    | exact superpose eq386 eq26553
    | exact resolve eq26553 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26553
  have eq26631 : ∀ X0 X1 : G, (k X1 (σ y)) = (M.op (k X0 (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26601 X0 X1
       have i₂ := eq25980 X1
       grind)
    | exact superpose eq25980 eq26601
    | exact resolve eq26601 eq25980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25980 eq26601
  have eq30115 : ∀ X0 X1 : G, (τ (k X1 (σ y))) = (k (τ (M.op X0 (M.op X0 X1))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq26494 X0 (M.op X0 X1)
       have i₂ := eq26631 X0 X1
       grind)
    | exact superpose eq26631 eq26494
    | exact resolve eq26494 eq26631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26494 eq26631
  have eq30189 : ∀ X0 X1 : G, (τ (k X1 (σ y))) = (k (τ (M.op (k X0 X0) X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq30115 X0 X1
       have i₂ := eq485 X0 X1
       grind)
    | exact superpose eq485 eq30115
    | exact resolve eq30115 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30115
  have eq30219 : ∀ X0 X1 : G, (k (τ X1) y) = (k (τ (M.op (k X0 X0) X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq30189 X0 X1
       have i₂ := eq23 X1 y
       grind)
    | exact superpose eq23 eq30189
    | exact resolve eq30189 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30189
  have eq48757 : ∀ X0 X1 X2 : G, (k X2 (σ (τ (k X0 X0)))) = X2 ∨ (M.op X1 X2) = (k (k X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq664 X2 (τ X0) X1
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq664
    | (have j0 := eq664 X2 X1 X1
       grind)
    | exact resolve eq664 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq664
  have eq48761 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (k X2 X2) X1) ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48757 X0 X1 X2
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq48757
    | (have j0 := eq48757 X0 X1 X2
       grind)
    | exact resolve eq48757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48757
  have eq48862 : ∀ X0 X1 X2 X3 : G, (k (k X0 X0) X3) = (k (M.op (k X2 X2) X0) X3) ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3049 X2 X0 X3
       have i₂ := eq48761 X1 (k X2 X2) X0
       grind)
    | exact superpose eq48761 eq3049
    | (have j1 := eq48761 X1 X1 X0
       grind)
    | exact resolve eq3049 eq48761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049 eq48761
  have eq49248 : ∀ X0 X1 X2 : G, (σ X1) = (k (σ X1) (k X2 X2)) ∨ (M.op X0 X1) = (k (k X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (k X2 X2) X1
       have i₂ := eq665 X1 X2 X0
       grind)
    | exact superpose eq665 eq19
    | (have j1 := eq665 X1 X1 X0
       grind)
    | exact resolve eq19 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq49249 : ∀ X0 X1 : G, (σ (k X0 (k X0 X0))) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq49248 eq6526
    | (have j0 := eq6526 X0 X1
       have j1 := eq49248 X0 X0 X1
       grind)
    | exact resolve eq6526 eq49248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526 eq49248
  have eq49254 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (k (σ X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49249 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq49249
    | (have j0 := eq49249 X0 X1
       grind)
    | exact resolve eq49249 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49249
  have eq62459 : ∀ X0 X1 : G, y = (M.op (k (k X0 X0) (k X0 X0)) y) ∨ (k X1 y) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq137 (k X0 X0) X1 y
       have i₂ := eq6614 X0
       grind)
    | exact superpose eq6614 eq137
    | (have j0 := eq137 X0 X1 y
       grind)
    | exact resolve eq137 eq6614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq62466 : ∀ X0 X1 : G, y = (M.op (k X0 X0) y) ∨ (k X1 y) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62459 X0 X1
       have i₂ := eq386 X0 (k X0 X0) y
       grind)
    | (have i₁ := eq62459 X0 X1
       have i₂ := eq386 X0 (k (k X0 X0) (k X0 X0)) y
       grind)
    | exact superpose eq386 eq62459
    | (have j0 := eq62459 X0 X1
       grind)
    | exact resolve eq62459 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq62459
  have eq77248 : ∀ X0 X1 : G, (M.op (k X1 X1) X0) ≠ X0 ∨ (k X0 (k (k X1 X1) (k X1 X1))) = (M.op (k X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq6449 (k X1 X1) X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6449
  have eq77249 : ∀ X0 X1 : G, (M.op (k X1 X1) X0) ≠ X0 ∨ (k X0 (k (k X1 X1) (k X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq77248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77248
  have eq77250 : ∀ X0 X1 : G, (M.op (k X1 X1) X0) ≠ X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77249 X0 X1
       have i₂ := eq118 X1
       grind)
    | exact superpose eq118 eq77249
    | (have j0 := eq77249 X0 X1
       grind)
    | exact resolve eq77249 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq77249
  have eq77268 : ∀ X0 X1 : G, (k (k X0 X0) X1) = (k (k (k X0 X0) X1) (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77250 (k (k X0 X0) X1) X1
       grind)
    | (have r₁ := eq77250 (k (k X0 X0) X1) X1
       have r₂ := eq140 X0 X1
       grind)
    | exact resolve eq77250 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq77284 : ∀ X0 : G, (k (k X0 X0) X0) ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq77250 X0 X0
       have i₂ := eq745 X0
       grind)
    | exact superpose eq745 eq77250
    | (have j0 := eq77250 X0 X0
       grind)
    | exact resolve eq77250 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77250
  have eq84769 : ∀ X0 X1 X2 : G, (k X1 X0) = (k (k X1 X1) X0) ∨ (k X1 (k X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5750 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5750
    | (have j0 := eq5750 X1 X2 X2
       grind)
    | exact resolve eq5750 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5750
  have eq84792 : ∀ X0 X1 X2 X3 : G, (k X0 X3) = (k (M.op (k X2 X2) X0) X3) ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq84769 eq48862
    | (have j0 := eq48862 X0 X1 X2 X3
       have j1 := eq84769 X0 X0 X1
       grind)
    | exact resolve eq48862 eq84769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48862 eq84769
  have eq85211 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (k (k X0 X0) X0) X1) ∨ (k X0 (k X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84792 X0 X2 X0 X1
       have i₂ := eq745 X0
       grind)
    | exact superpose eq745 eq84792
    | (have j0 := eq84792 X0 X2 X2 x
       grind)
    | exact resolve eq84792 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq84792
  have eq86426 : ∀ X0 X1 : G, (k (k X0 X0) X0) = (k X0 (k X0 X0)) ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85211 X0 (k X0 X0) X1
       have i₂ := eq77268 X0 X0
       grind)
    | exact superpose eq77268 eq85211
    | (have j0 := eq85211 X0 X1 X1
       grind)
    | exact resolve eq85211 eq77268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77268 eq85211
  have eq86679 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (τ (τ (σ (k X1 X1))))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14291 X0 (σ X1)
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq14291
    | (have j0 := eq14291 X0 X1
       grind)
    | exact resolve eq14291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14291
  have eq86688 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (τ (k X1 X1))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86679 X0 X1
       have i₂ := eq10 (k X1 X1)
       grind)
    | exact superpose eq10 eq86679
    | (have j0 := eq86679 X0 X1
       grind)
    | exact resolve eq86679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86679
  have eq86709 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (τ (σ (k X1 X1)))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86688 X0 (σ X1)
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq86688
    | (have j0 := eq86688 X0 X1
       grind)
    | exact resolve eq86688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86688
  have eq86718 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (k X1 X1)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86709 X0 X1
       have i₂ := eq10 (k X1 X1)
       grind)
    | exact superpose eq10 eq86709
    | (have j0 := eq86709 X0 X1
       grind)
    | exact resolve eq86709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86709
  have eq86723 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (k X1 X1)) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq86718 eq49254
    | (have j0 := eq49254 X0 X1
       have j1 := eq86718 X0 X1
       grind)
    | exact resolve eq49254 eq86718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49254 eq86718
  have eq86890 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86723 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86723
    | exact resolve eq86723 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86723
  have eq86900 : ∀ X0 X1 : G, (k X0 (σ (k (τ X0) (τ X0)))) = X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86890 X0 X1
       have i₂ := eq18 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq86890
    | (have j0 := eq86890 X0 X1
       grind)
    | exact resolve eq86890 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq86890
  have eq86901 : ∀ X0 X1 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86900 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq86900
    | (have j0 := eq86900 X0 X1
       grind)
    | exact resolve eq86900 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq86900
  have eq86902 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86901 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86901
    | (have j0 := eq86901 X0 X0
       grind)
    | exact resolve eq86901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86901
  have eq86903 : ∀ X0 X1 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq86902 eq86426
    | (have j0 := eq86426 X0 X1
       have j1 := eq86902 X0 X1
       grind)
    | exact resolve eq86426 eq86902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86426 eq86902
  have eq86911 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq77284 X0
       have j1 := eq86903 X0 X0
       grind)
    | (have r₁ := eq77284 X0
       have r₂ := eq86903 X0 x
       grind)
    | exact resolve eq77284 eq86903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77284 eq86903
  have eq125291 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) ∨ (k X2 (τ X0)) = (M.op (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq241 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq241
    | (have j0 := eq241 X2 (τ X0) X2
       grind)
    | exact resolve eq241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq125306 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq125291 X0 X0 x
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq125291
    | (have j0 := eq125291 X0 X1 X1
       grind)
    | exact resolve eq125291 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq125291
  have eq125333 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125306 X0 X1
       have i₂ := eq86911 X0
       grind)
    | exact superpose eq86911 eq125306
    | (have j0 := eq125306 X0 X1
       grind)
    | exact resolve eq125306 eq86911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86911 eq125306
  have eq125973 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq125333 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq125333
    | (have j0 := eq125333 (σ X0) X1
       grind)
    | exact resolve eq125333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125333
  have eq126016 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq125973 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq125973
    | (have j0 := eq125973 X0 X1
       grind)
    | exact resolve eq125973 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125973
  have eq126022 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | exact superpose eq126016 eq19243
    | (have j1 := eq126016 x x
       grind)
    | exact resolve eq19243 eq126016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19243 eq126016
  have eq126055 : (σ x) = (σ (k x x)) := by grind
  clear eq126022
  have eq126083 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq395 x X1 X0
       have i₂ := eq126055
       grind)
    | exact superpose eq126055 eq395
    | exact resolve eq395 eq126055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq126516 : (k x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq126055
       grind)
    | exact superpose eq126055 eq10
    | exact resolve eq10 eq126055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126055
  have eq126693 : x = (k x x) := by
    first
    | (have i₁ := eq126516
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq126516
    | exact resolve eq126516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126516
  have eq126943 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (M.op x (τ (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq4106 x X0
       have i₂ := eq126693
       grind)
    | exact superpose eq126693 eq4106
    | exact resolve eq4106 eq126693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106
  have eq126984 : y = (k y x) := by
    first
    | (have i₁ := eq6614 x
       have i₂ := eq126693
       grind)
    | exact superpose eq126693 eq6614
    | exact resolve eq6614 eq126693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq127530 : ∀ X0 : G, (k (τ X0) y) = (k (τ (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq30219 x X0
       have i₂ := eq126693
       grind)
    | exact superpose eq126693 eq30219
    | exact resolve eq30219 eq126693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30219
  have eq127928 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq62466 x X0
       have i₂ := eq126693
       grind)
    | exact superpose eq126693 eq62466
    | (have j0 := eq62466 X0 X0
       grind)
    | exact resolve eq62466 eq126693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62466 eq126693
  have eq128260 : ∀ X0 : G, (σ y) ≠ (σ (k y x)) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | exact superpose eq127928 eq19564
    | (have j0 := eq19564 X0
       have j1 := eq127928 X0
       grind)
    | exact resolve eq19564 eq127928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19564 eq127928
  have eq128348 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq128260 X0
       have i₂ := eq126984
       grind)
    | exact superpose eq126984 eq128260
    | (have j0 := eq128260 X0
       grind)
    | exact resolve eq128260 eq126984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126984 eq128260
  have eq128349 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq128348 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128348
  have eq129142 : ∀ X0 : G, (M.op (k y y) X0) = (M.op y (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq485 y X0
       have i₂ := eq128349 X0
       grind)
    | exact superpose eq128349 eq485
    | exact resolve eq485 eq128349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq129599 : ∀ X0 : G, (M.op (k y y) X0) = (k (k X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq129142 X0
       have i₂ := eq128349 (k X0 y)
       grind)
    | exact superpose eq128349 eq129142
    | exact resolve eq129142 eq128349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128349 eq129142
  have eq140941 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (k X0 y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 y X1 X0
       have i₂ := eq129599 X0
       grind)
    | exact superpose eq129599 eq391
    | exact resolve eq391 eq129599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq129599
  have eq144901 : ∀ X0 X1 : G, (M.op X1 (τ (M.op x X0))) = (M.op X1 (k (k (τ X0) y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq140941 (τ (M.op x X0)) X1
       have i₂ := eq127530 X0
       grind)
    | exact superpose eq127530 eq140941
    | exact resolve eq140941 eq127530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127530
  have eq145154 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq144901 X0 X1
       have i₂ := eq140941 (τ X0) X1
       grind)
    | exact superpose eq140941 eq144901
    | exact resolve eq144901 eq140941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140941 eq144901
  have eq146877 : ∀ X0 X1 : G, (M.op X1 (τ (M.op x X0))) = (M.op X1 (τ (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq145154 (M.op (σ x) X0) X1
       have i₂ := eq126083 X0 x
       grind)
    | exact superpose eq126083 eq145154
    | exact resolve eq145154 eq126083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126083
  have eq147110 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op (σ x) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq146877 X0 X1
       have i₂ := eq145154 X0 X1
       grind)
    | exact superpose eq145154 eq146877
    | exact resolve eq146877 eq145154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145154 eq146877
  have eq147137 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq126943 X0
       have i₂ := eq147110 X0 x
       grind)
    | exact superpose eq147110 eq126943
    | exact resolve eq126943 eq147110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126943 eq147110
  have eq147240 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ x) X0)
       have i₂ := eq147137 X0
       grind)
    | exact superpose eq147137 eq11
    | exact resolve eq11 eq147137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147137
  have eq147373 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq147240 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq147240
    | exact resolve eq147240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147240
  have eq147418 : False := by grind
  exact eq147418

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation882 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  clear eq18
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq28
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq98 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq5788 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq98 X1 X0
       grind)
    | exact superpose eq98 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq98 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X1
       have r₂ := eq98 (M.op X1 (σ X1)) X1
       grind)
    | exact resolve eq13 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq5842 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5788
  have eq5843 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5842 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5842
  have eq7683 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5843 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5843
    | exact resolve eq5843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7716 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq5843 X0 X1
       grind)
    | exact superpose eq5843 eq37
    | (have j1 := eq5843 X0 X1
       grind)
    | exact resolve eq37 eq5843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5843
  have eq7809 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7716 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7716
    | (have j0 := eq7716 X0 X1
       grind)
    | exact resolve eq7716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7716
  have eq7817 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7683 X0 X1
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq7683
    | (have j0 := eq7683 X0 X1
       grind)
    | exact resolve eq7683 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq7683
  have eq7961 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq7817 X1 X0
       grind)
    | exact superpose eq7817 eq11
    | (have j1 := eq7817 X1 X0
       grind)
    | exact resolve eq11 eq7817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7817
  have eq8083 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7961 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq7961
    | (have j0 := eq7961 X0 X1
       grind)
    | exact resolve eq7961 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7961
  have eq8123 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq8083 (τ X0) X1
       grind)
    | exact superpose eq8083 eq19
    | (have j1 := eq8083 (τ X0) X1
       grind)
    | exact resolve eq19 eq8083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8083
  have eq8373 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq7809 X0 X1
       grind)
    | exact superpose eq7809 eq11
    | (have j1 := eq7809 X0 X1
       grind)
    | exact resolve eq11 eq7809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7809
  have eq8448 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8373 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq8373
    | (have j0 := eq8373 X0 X1
       grind)
    | exact resolve eq8373 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8373
  have eq8510 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq8448 X1 (σ X0)
       grind)
    | exact superpose eq8448 eq15
    | (have j1 := eq8448 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq8448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8448
  have eq8580 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8510 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8510
    | (have j0 := eq8510 X0 X1
       grind)
    | exact resolve eq8510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8510
  have eq9711 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8123 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8123
    | exact resolve eq8123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8123
  have eq9808 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9711 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9711
    | (have j0 := eq9711 X0 X1
       grind)
    | exact resolve eq9711 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9711
  have eq10148 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8580 x y
       grind)
    | exact superpose eq8580 eq16
    | (have j1 := eq8580 x y
       grind)
    | exact resolve eq16 eq8580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8580
  have eq10327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10148
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq10148
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq10148
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10148
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10148 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10328 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq10148
       have i₂ := eq9808 x y
       grind)
    | exact superpose eq9808 eq10148
    | (have j1 := eq9808 x y
       grind)
    | (have r₁ := eq10148
       have r₂ := eq9808 x y
       grind)
    | (have r₁ := eq10148
       have r₂ := eq9808 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10148
       have r₂ := eq9808 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10148 eq9808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9808 eq10148
  have eq10331 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10328
  have eq10332 : x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq10331
  have eq10333 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10327
  have eq10334 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq10333
  have eq10338 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10332
       grind)
    | exact superpose eq10332 eq16
    | exact resolve eq16 eq10332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10332
  have eq10339 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10338
       have r₂ := eq22 x
       grind)
    | exact resolve eq10338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10338
  have eq10433 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq271 x y
       have i₂ := eq10339
       grind)
    | exact superpose eq10339 eq271
    | (have j0 := eq271 x y
       grind)
    | exact resolve eq271 eq10339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq10339
  have eq10452 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10433
  have eq10453 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10452
  have eq10460 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10334
       grind)
    | exact superpose eq10334 eq16
    | exact resolve eq16 eq10334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10334
  have eq10461 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10460
       have r₂ := eq22 x
       grind)
    | exact resolve eq10460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10460
  have eq10597 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10453
       grind)
    | exact superpose eq10453 eq10
    | exact resolve eq10 eq10453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10453
  have eq10670 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10597
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10597
    | exact resolve eq10597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10597
  have eq10759 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10670
       grind)
    | exact superpose eq10670 eq16
    | exact resolve eq16 eq10670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10670
  have eq10760 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10759
       have r₂ := eq22 x
       grind)
    | exact resolve eq10759 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10759
  have eq10768 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10760
       grind)
    | exact superpose eq10760 eq16
    | exact resolve eq16 eq10760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10760
  have eq10934 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10768
       have i₂ := eq10461
       grind)
    | exact superpose eq10461 eq10768
    | exact resolve eq10768 eq10461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10461 eq10768
  have eq10937 : (σ x) = (σ y) := by grind
  clear eq10934
  have eq10939 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10937
       grind)
    | exact superpose eq10937 eq16
    | exact resolve eq16 eq10937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10940 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10937
       grind)
    | exact superpose eq10937 eq10
    | exact resolve eq10 eq10937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10937
  have eq11013 : x = y := by
    first
    | (have i₁ := eq10940
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10940
    | exact resolve eq10940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10940
  have eq11014 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10939
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq10939
    | exact resolve eq10939 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10939
  have eq11016 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11014
       have i₂ := eq11013
       grind)
    | exact superpose eq11013 eq11014
    | exact resolve eq11014 eq11013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11013 eq11014
  have eq11017 : False := by grind
  exact eq11017
