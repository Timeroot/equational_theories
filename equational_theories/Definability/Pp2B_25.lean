import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_x_pyx_pxy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq23
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
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
  have eq69 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X5 (M.op X0 (M.op X4 X2)))) X5) = (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 X3 X4 (M.op X0 (M.op X4 X2)) X5
       have i₂ := eq62 X0 X1 X2 X4
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq62 X0 x X2 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq62 (M.op X0 X1) X2 X1 x
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) X2 X3
       have i₂ := eq79 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq79 eq79
    | exact resolve eq79 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (M.op X0 (M.op (M.op X1 X2) X1)) X1 X2
       have i₂ := eq79 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq79 eq79
    | exact resolve eq79 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op (M.op X3 X0) (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X0 X1 X2 X3 X4 x
       have i₂ := eq92 X3 x X0 (M.op X4 X2)
       grind)
    | exact superpose eq92 eq69
    | exact resolve eq69 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq92
  have eq126 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 X2 x
       have i₂ := eq114 X0 x X2 (M.op X1 X2) X0
       grind)
    | exact superpose eq114 eq63
    | exact resolve eq63 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq114
  have eq133 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X2 (M.op X0 X1) (M.op X2 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq126
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X1 (M.op X0 (M.op X2 X1)) X2
       have i₂ := eq79 X0 X2 X1
       grind)
    | exact superpose eq79 eq126
    | exact resolve eq126 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (M.op (M.op X0 X2) X1) X1 X2
       have i₂ := eq126 X1 X0 X2
       grind)
    | exact superpose eq126 eq79
    | exact resolve eq79 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X4) X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X1 X2 (M.op X3 X4) (M.op (M.op X0 X4) X3)
       have i₂ := eq126 X3 X0 X4
       grind)
    | exact superpose eq126 eq62
    | exact resolve eq62 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq153 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X4) X3)) = (M.op (M.op X1 X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq151 X0 X1 x X3 X4
       have i₂ := eq91 X1 x X3 X4
       grind)
    | exact superpose eq91 eq151
    | exact resolve eq151 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq151
  have eq880 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 X2) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq145 (M.op X0 X2) X3 X1
       have i₂ := eq145 X0 X2 X1
       grind)
    | (have i₁ := eq145 (M.op X0 X2) X3 X1
       have i₂ := eq145 X0 X1 X2
       grind)
    | exact superpose eq145 eq145
    | exact resolve eq145 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq134 X3 (M.op X0 X2) X1
       have i₂ := eq145 X0 X2 X1
       grind)
    | (have i₁ := eq134 X3 (M.op X0 X2) X1
       have i₂ := eq145 X0 X1 X2
       grind)
    | exact superpose eq145 eq134
    | exact resolve eq134 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq966 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X0 X1 X2
       have i₂ := eq947 X1 X2 X1 X0
       grind)
    | exact superpose eq947 eq95
    | exact resolve eq95 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq982 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X3) X4) = (M.op (M.op X1 X0) (M.op X4 (M.op X0 X3))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq153 X0 X1 X3 X4
       have i₂ := eq947 X0 X4 X3 (M.op X1 X0)
       grind)
    | exact superpose eq947 eq153
    | exact resolve eq153 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq947
  have eq1141 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X0 X1 (M.op X2 X2)
       have i₂ := eq966 X0 X2 X1
       grind)
    | exact superpose eq966 eq79
    | exact resolve eq79 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1143 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133 X1 (M.op X0 X0) X2
       have i₂ := eq966 X2 X0 X2
       grind)
    | exact superpose eq966 eq133
    | exact resolve eq133 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq1165 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X2 X0 (M.op X1 X1)
       have i₂ := eq966 (M.op (M.op X0 (M.op X1 X1)) X2) X1 X2
       grind)
    | exact superpose eq966 eq126
    | exact resolve eq126 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1166 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X0 X1 (M.op X2 X2)
       have i₂ := eq966 (M.op (M.op X0 X1) (M.op X2 X2)) X2 X1
       grind)
    | exact superpose eq966 eq83
    | exact resolve eq83 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2386 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq2405 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) X1) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    grind
  have eq2432 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386
  have eq2440 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X0) (M.op X1 (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2405 X0 X1
       have i₂ := eq880 X0 X1 X0 (M.op X1 (M.op X0 X0))
       grind)
    | (have i₁ := eq2405 X1 x
       have i₂ := eq880 X1 X1 (M.op x (M.op X1 X1)) x
       grind)
    | exact superpose eq880 eq2405
    | (have j0 := eq2405 X0 X1
       grind)
    | exact resolve eq2405 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq2405
  have eq2449 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2432 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq2432 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2432 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2432
  have eq2460 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X0) X1) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2440 X0 X1
       have i₂ := eq982 X0 (M.op X0 X1) X0 X1
       grind)
    | (have i₁ := eq2440 x X1
       have i₂ := eq982 X0 (M.op x X1) x (M.op X1 (M.op x x))
       grind)
    | exact superpose eq982 eq2440
    | (have j0 := eq2440 X0 X1
       grind)
    | exact resolve eq2440 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq2440
  have eq2537 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2449 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2538 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2449 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq2589 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2537 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq2537 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq2537
    | (have j0 := eq2537 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq2537 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq2537 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2591 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2537 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537
  have eq2593 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2589 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2589
  have eq2599 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2593 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq2593 (M.op (k X1 X1) (k X1 X1)) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq2593 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2593 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2593
  have eq2620 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2599 X0 X1
       have i₂ := eq2591 X1
       grind)
    | exact superpose eq2591 eq2599
    | (have j0 := eq2599 X0 X1
       grind)
    | exact resolve eq2599 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599
  have eq2655 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2591 (σ X0)
       grind)
    | exact superpose eq2591 eq15
    | exact resolve eq15 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2657 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq2591 (τ X0)
       grind)
    | exact superpose eq2591 eq32
    | exact resolve eq32 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2666 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2657 X0
       have i₂ := eq2591 X0
       grind)
    | exact superpose eq2591 eq2657
    | exact resolve eq2657 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2657
  have eq2668 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2655 X0
       have i₂ := eq2591 X0
       grind)
    | exact superpose eq2591 eq2655
    | exact resolve eq2655 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591 eq2655
  have eq2723 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1143 X2 X1 (τ X0)
       have i₂ := eq2666 X0
       grind)
    | exact superpose eq2666 eq1143
    | exact resolve eq1143 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq2725 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (τ (M.op X0 X0))) X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1166 X1 X2 (τ X0)
       have i₂ := eq2666 X0
       grind)
    | exact superpose eq2666 eq1166
    | exact resolve eq1166 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq2758 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1141 (σ X0) (σ X0) X1
       have i₂ := eq2668 X0
       grind)
    | exact superpose eq2668 eq1141
    | exact resolve eq1141 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq2766 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq2668 X0
       grind)
    | exact superpose eq2668 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2768 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq966 X1 (σ X0) X2
       have i₂ := eq2668 X0
       grind)
    | exact superpose eq2668 eq966
    | exact resolve eq966 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq2777 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2766 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq2766 X0 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       have r₂ := eq12 (σ (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq2766 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2766 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq3400 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2723 (τ X0) X1 X2
       have i₂ := eq2666 X0
       grind)
    | exact superpose eq2666 eq2723
    | exact resolve eq2723 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723
  have eq3964 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (τ (τ (M.op X0 X0)))) X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2725 (τ X0) X1 X2
       have i₂ := eq2666 X0
       grind)
    | exact superpose eq2666 eq2725
    | exact resolve eq2725 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq4194 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (σ (M.op X2 X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X0 X1 (σ (M.op X2 X2))
       have i₂ := eq2768 X2 X0 X1
       grind)
    | exact superpose eq2768 eq134
    | exact resolve eq134 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq2768
  have eq7888 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3400 (τ X0) X1 X2
       have i₂ := eq2666 X0
       grind)
    | exact superpose eq2666 eq3400
    | exact resolve eq3400 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400
  have eq8735 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (τ (τ (τ (M.op X0 X0))))) X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3964 (τ X0) X1 X2
       have i₂ := eq2666 X0
       grind)
    | exact superpose eq2666 eq3964
    | exact resolve eq3964 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2666 eq3964
  have eq20959 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) ≠ (M.op X0 (τ (τ (τ (M.op X1 X1))))) ∨ (M.op (M.op X2 X2) X0) = (k (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2538 (M.op X2 X2) X0
       have i₂ := eq7888 X1 X0 X2
       grind)
    | exact superpose eq7888 eq2538
    | (have j0 := eq2538 (M.op X2 X2) X0
       grind)
    | exact resolve eq2538 eq7888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538 eq7888
  have eq28006 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X0 (τ (τ (τ (M.op X1 X1))))) ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8735 X1 (M.op X0 (τ (τ (τ (M.op X1 X1))))) X0
       have i₂ := eq2460 X0 (τ (τ (τ (M.op X1 X1))))
       grind)
    | exact superpose eq2460 eq8735
    | (have j1 := eq2460 X0 X1
       grind)
    | exact resolve eq8735 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460 eq8735
  have eq28157 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq28006 X0 x
       have j1 := eq20959 X0 x X0
       grind)
    | (have r₁ := eq28006 X0 x
       have r₂ := eq20959 X0 x X0
       grind)
    | exact resolve eq28006 eq20959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20959 eq28006
  have eq28626 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28157 (σ X0)
       have i₂ := eq2668 X0
       grind)
    | exact superpose eq2668 eq28157
    | exact resolve eq28157 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq28645 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq28626 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq28626
    | exact resolve eq28626 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28626
  have eq28694 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq28645 X0
       have i₂ := eq28157 X0
       grind)
    | exact superpose eq28157 eq28645
    | exact resolve eq28645 eq28157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28157 eq28645
  have eq28740 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2758 X0 X1
       have i₂ := eq28694 X0
       grind)
    | exact superpose eq28694 eq2758
    | exact resolve eq2758 eq28694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758 eq28694
  have eq29368 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28740 (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq1165 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq1165 eq28740
    | exact resolve eq28740 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165 eq28740
  have eq32714 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29368 X0 X1 x
       have i₂ := eq29368 X0 X2 x
       grind)
    | exact superpose eq29368 eq29368
    | exact resolve eq29368 eq29368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32809 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ X0) (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4194 (σ X0) (σ (M.op X2 X2)) X2
       have i₂ := eq29368 X0 X1 (σ (M.op X2 X2))
       grind)
    | exact superpose eq29368 eq4194
    | exact resolve eq4194 eq29368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4194 eq29368
  have eq315571 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq2777 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq2777 X0 (σ X0)
       grind)
    | exact superpose eq2777 eq10
    | (have j1 := eq2777 X1 X0
       grind)
    | exact resolve eq10 eq2777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq353437 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq315571 (σ X1) X0
       grind)
    | exact superpose eq315571 eq15
    | (have j1 := eq315571 (σ X1) X0
       grind)
    | exact resolve eq15 eq315571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315571
  have eq353463 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq353437 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq353437
    | (have j0 := eq353437 X0 X1
       grind)
    | exact resolve eq353437 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353437
  have eq488649 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq353463 x y
       grind)
    | exact superpose eq353463 eq16
    | (have j1 := eq353463 x y
       grind)
    | exact resolve eq16 eq353463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353463
  have eq490273 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq488649
       have i₂ := eq2620 y x
       grind)
    | exact superpose eq2620 eq488649
    | (have j1 := eq2620 y x
       grind)
    | exact resolve eq488649 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620 eq488649
  have eq490277 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq490273
  have eq490278 : y = (M.op x x) := by grind
  clear eq490277
  have eq490417 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq32714 X0 X1 x
       have i₂ := eq490278
       grind)
    | exact superpose eq490278 eq32714
    | exact resolve eq32714 eq490278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32714
  have eq490420 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ X0) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq32809 X0 X1 x
       have i₂ := eq490278
       grind)
    | exact superpose eq490278 eq32809
    | exact resolve eq32809 eq490278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32809 eq490278
  have eq500130 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq490420 X0 x
       have i₂ := eq490417 X0 x
       grind)
    | exact superpose eq490417 eq490420
    | exact resolve eq490420 eq490417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490417 eq490420
  have eq512951 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq500130 x
       grind)
    | exact superpose eq500130 eq16
    | (have r₁ := eq16
       have r₂ := eq500130 x
       grind)
    | exact resolve eq16 eq500130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500130
  have eq512952 : False := by grind
  exact eq512952

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_pxx_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X2 X1))) ≠ X0 ∨ (k (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) (M.op X2 X1)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X1 X2))) ≠ X0 ∨ (M.op X1 (M.op (M.op X0 X2) (M.op X1 X2))) = (k X1 (M.op (M.op X0 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X2) (M.op X1 X2))
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 X2) (M.op X1 X2))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq101 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq102 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq106 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq102
    | exact resolve eq102 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq106
    | exact resolve eq106 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
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
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq135
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq135
    | exact resolve eq135 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq138
    | exact resolve eq138 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq147 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq108
       grind)
    | exact superpose eq108 eq16
    | exact resolve eq16 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq181 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 X1) (M.op y X1))) := by
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
  have eq245 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op (M.op x y) (M.op X1 y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 (M.op x y)) x) := by
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
  have eq301 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq34
    | exact resolve eq34 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq312 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq301
    | exact resolve eq301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq314 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq312 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq312
    | exact resolve eq312 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq312
  have eq447 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 (M.op X2 (M.op (M.op x y) (M.op X1 y)))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4) (M.op X3 X4)) := by
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
  have eq464 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 X1) y)) X2) (M.op X1 X2)) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
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
  have eq468 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
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
  have eq476 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) (M.op X0 X4)) = X3 := by
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
  have eq532 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
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
  have eq549 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) (M.op (σ x) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) (M.op X0 (M.op X5 X2))) (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X4 X5))) = X3 := by
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
  have eq571 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X3 := by
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
  have eq575 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
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
  have eq583 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X5 (M.op (M.op X0 X4) X2))) X5) := by
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
  have eq815 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq468 eq65
    | exact resolve eq65 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq469 eq65
    | exact resolve eq65 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq860 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq16
    | exact resolve eq16 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : (M.op x y) ≠ (M.op y x) ∨ (M.op y x) = (k y x) := by
    first
    | exact superpose eq468 eq66
    | exact resolve eq66 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1143 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq469 eq66
    | exact resolve eq66 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq469
  have eq1282 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq253 eq467
    | exact resolve eq467 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1293 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 (M.op X0 X1) X2 (M.op X1 X2)
       have i₂ := eq467 X0 X1 X2
       grind)
    | exact superpose eq467 eq467
    | exact resolve eq467 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 (M.op X0 X1) (M.op X2 X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq467
    | exact resolve eq467 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 y) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq467
    | exact resolve eq467 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1296 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq467
    | exact resolve eq467 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1306 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq54 eq467
    | exact resolve eq467 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1741 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq253 eq575
    | exact resolve eq575 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq1746 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq575 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq575
    | (have j0 := eq575 X0 x y
       grind)
    | exact resolve eq575 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1750 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq575
    | (have j0 := eq575 X0 (σ x) (σ y)
       grind)
    | exact resolve eq575 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1754 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq575 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq471 X0 X2 X2
       grind)
    | exact superpose eq471 eq575
    | exact resolve eq575 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1760 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq575 (M.op (M.op X0 (M.op X1 X2)) X2) X1 X2
       have i₂ := eq467 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq467 eq575
    | exact resolve eq575 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1811 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op x sF3)
       have i₂ := eq575 sF4 x sF3
       grind)
    | exact superpose eq575 eq51
    | exact resolve eq51 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2230 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) (M.op (M.op (M.op X0 X1) (M.op y X1)) y))) := by
    intro X0 X1
    first
    | exact superpose eq240 eq245
    | exact resolve eq245 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq245
  have eq2317 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2230 X0 x
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq2230
    | exact resolve eq2230 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2320 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) y) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq1746 (M.op (M.op X0 sF0) y)
       have i₂ := eq467 X0 sF0 y
       grind)
    | exact superpose eq467 eq1746
    | exact resolve eq1746 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2368 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq1746 eq50
    | exact resolve eq50 eq1746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1746
  have eq2602 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1750 (M.op (M.op X0 sF4) sF3)
       have i₂ := eq467 X0 sF4 sF3
       grind)
    | exact superpose eq467 eq1750
    | exact resolve eq1750 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2657 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1750 eq51
    | exact resolve eq51 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1750
  have eq2690 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2657 eq467
    | exact resolve eq467 eq2657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2712 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2657 eq575
    | exact resolve eq575 eq2657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2657
  have eq2713 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1306 eq2712
    | exact resolve eq2712 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306 eq2712
  have eq2955 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1811 eq471
    | exact resolve eq471 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3439 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op X1 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 x
       have i₂ := eq52 X0 x y X1
       grind)
    | exact superpose eq52 eq270
    | exact resolve eq270 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3991 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | exact superpose eq2320 eq467
    | exact resolve eq467 eq2320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq4268 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq2602 eq467
    | exact resolve eq467 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602
  have eq5715 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    first
    | exact superpose eq2713 eq1811
    | exact resolve eq1811 eq2713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2713
  have eq5720 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2955 eq5715
    | exact resolve eq5715 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5715
  have eq7404 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5720 eq471
    | exact resolve eq471 eq5720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5720
  have eq12341 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1295 (M.op (M.op y (M.op X0 X0)) X0)
       have i₂ := eq571 y X0 X0 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq571 eq1295
    | exact resolve eq1295 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq12342 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1296 (M.op (M.op sF3 (M.op x x)) x)
       have i₂ := eq571 sF3 x x (M.op sF3 (M.op x x))
       grind)
    | exact superpose eq571 eq1296
    | exact resolve eq1296 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq1296
  have eq12604 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12341 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12341
    | exact resolve eq12341 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12605 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12341 (τ X0)
       have i₂ := eq860 X0
       grind)
    | exact superpose eq860 eq12341
    | exact resolve eq12341 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12341
  have eq12699 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12342 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12342
    | exact resolve eq12342 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq12709 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq12342 eq471
    | exact resolve eq471 eq12342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12342
  have eq13115 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12709 (τ X0)
       have i₂ := eq860 X0
       grind)
    | exact superpose eq860 eq12709
    | exact resolve eq12709 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq13136 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq12709 eq471
    | exact resolve eq471 eq12709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq12709
  have eq19851 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 y) y)) (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq464 eq270
    | exact resolve eq270 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq464
  have eq19961 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq19851 x
       have i₂ := eq575 sF0 x y
       grind)
    | exact superpose eq575 eq19851
    | exact resolve eq19851 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq19851
  have eq25310 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1754 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X2
       have i₂ := eq467 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq467 eq1754
    | exact resolve eq1754 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754
  have eq25944 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1760 (M.op (M.op X0 X2) X1) X2 X1
       have i₂ := eq467 X0 X2 X1
       grind)
    | exact superpose eq467 eq1760
    | exact resolve eq1760 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq1760
  have eq30700 : ∀ X0 : G, (M.op (M.op x x) X0) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2317 (M.op x sF0)
       have i₂ := eq1293 (M.op x x) x sF0
       grind)
    | exact superpose eq1293 eq2317
    | exact resolve eq2317 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq32785 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op X1 (σ x)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq549
    | (have j0 := eq549 X0 X1 (σ x)
       grind)
    | exact resolve eq549 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq33273 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32785 X0 X1
       have i₂ := eq1293 (M.op (M.op X0 X1) (M.op sF4 sF4)) X1 sF2
       grind)
    | exact superpose eq1293 eq32785
    | exact resolve eq32785 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32785
  have eq33349 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ x))) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1741 eq33273
    | exact resolve eq33273 eq1741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741 eq33273
  have eq60123 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X2 (M.op X0 X1) X1 x x
       have i₂ := eq463 X1 x X0 X1 x
       grind)
    | exact superpose eq463 eq532
    | exact resolve eq532 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq113100 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) (M.op X3 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq476 (M.op X2 X2) (M.op X1 X3) X2 (M.op X0 X1) (M.op X3 (M.op X1 X3))
       have i₂ := eq550 X2 X2 (M.op X1 X3) X0 X1 X3
       grind)
    | exact superpose eq550 eq476
    | exact resolve eq476 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq550
  have eq113414 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113100 X0 X1 X2 x
       have i₂ := eq1293 (M.op X2 X2) X1 x
       grind)
    | exact superpose eq1293 eq113100
    | exact resolve eq113100 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113100
  have eq133220 : ∀ X0 X2 X3 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op X2 y) (M.op x y)))) X3) := by
    intro X0 X2 X3
    first
    | exact superpose eq468 eq583
    | exact resolve eq583 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq583
  have eq136603 : ∀ X0 X2 X3 : G, (M.op (M.op X0 x) X2) = (M.op (M.op X0 (M.op X3 (M.op (M.op x y) (M.op X2 y)))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq133220 X0 X2 X2
       have i₂ := eq60123 (M.op X2 y) sF0 X2
       grind)
    | (have i₁ := eq133220 X0 X2 X2
       have i₂ := eq60123 sF0 (M.op X2 y) X2
       grind)
    | exact superpose eq60123 eq133220
    | exact resolve eq133220 eq60123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60123 eq133220
  have eq137529 : ∀ X0 X2 : G, (M.op (M.op X0 X2) x) = (M.op (M.op X0 x) X2) := by
    intro X0 X2
    first
    | exact superpose eq447 eq136603
    | exact resolve eq136603 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq136603
  have eq317636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq119 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq317636
    | exact resolve eq317636 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317636
  have eq317642 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq317637
       have r₂ := eq27
       grind)
    | exact resolve eq317637 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317637
  have eq317644 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq317642
    | exact resolve eq317642 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317642
  have eq317646 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq317644
    | exact resolve eq317644 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317644
  have eq317648 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq317646 eq1143
    | (have r₁ := eq1143
       have r₂ := eq317646
       grind)
    | exact resolve eq1143 eq317646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq317646
  have eq317921 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq317648
  have eq318311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq317921 eq119
    | exact resolve eq119 eq317921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq317921
  have eq318316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq318311
  have eq318318 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq318316
       have r₂ := eq27
       grind)
    | exact resolve eq318316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318316
  have eq318320 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1142
       have i₂ := eq318318
       grind)
    | exact superpose eq318318 eq1142
    | (have r₁ := eq1142
       have r₂ := eq318318
       grind)
    | exact resolve eq1142 eq318318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq318321 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq815
       have i₂ := eq318318
       grind)
    | exact superpose eq318318 eq815
    | (have r₁ := eq815
       have r₂ := eq318318
       grind)
    | exact resolve eq815 eq318318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq318318
  have eq318591 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq318321
  have eq318592 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq318320
  have eq318964 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq318591
       grind)
    | exact superpose eq318591 eq44
    | exact resolve eq44 eq318591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq318591
  have eq318978 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq318964
    | exact resolve eq318964 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318964
  have eq318982 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq318592
       grind)
    | exact superpose eq318592 eq101
    | exact resolve eq101 eq318592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq318592
  have eq318996 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq318982
    | exact resolve eq318982 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318982
  have eq319136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq318996 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq318996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318996
  have eq319139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq319136
    | exact resolve eq319136 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319136
  have eq319144 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq319139
       have r₂ := eq27
       grind)
    | exact resolve eq319139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319139
  have eq319146 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq319144
    | exact resolve eq319144 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319144
  have eq319147 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq319146
  have eq319150 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq319147
    | exact resolve eq319147 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319147
  have eq319270 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq319150 eq816
    | (have r₁ := eq816
       have r₂ := eq319150
       grind)
    | exact resolve eq816 eq319150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq319150
  have eq319541 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq319270
  have eq319813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq319541 eq318978
    | exact resolve eq318978 eq319541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318978 eq319541
  have eq319818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq319813
  have eq319820 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq319818
       have r₂ := eq27
       grind)
    | exact resolve eq319818 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319818
  have eq319984 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq319820 eq1811
    | exact resolve eq1811 eq319820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq319989 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq319820 eq2690
    | exact resolve eq2690 eq319820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690
  have eq320005 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq319820 eq7404
    | exact resolve eq7404 eq319820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7404 eq319820
  have eq320082 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2955 eq320005
    | exact resolve eq320005 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955 eq320005
  have eq320097 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq319989
    | exact resolve eq319989 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq319989
  have eq320299 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq320097 eq1282
    | exact resolve eq1282 eq320097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320097
  have eq322104 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (M.op (σ y) (σ y)) (M.op (M.op X0 X1) (σ y))) X2) (M.op X1 X2)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq320082 eq463
    | exact resolve eq463 eq320082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320082
  have eq322472 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq322104 x x x
       have i₂ := eq463 sF3 sF3 x x x
       grind)
    | exact superpose eq463 eq322104
    | exact resolve eq322104 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq322104
  have eq337180 : (M.op x y) = (M.op x (M.op y (τ (σ x)))) ∨ y = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f337180_12 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (τ (M.op X0 X0)))) := by
      intro X0
      grind
    have f337180_13 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f337180_21 : (M.op x y) ≠ (M.op x (M.op y (τ (σ x)))) := by grind
    have f337180_22 : y ≠ (M.op x y) := by grind
    have f337180_23 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (M.op X0 (σ y))) := by
      intro X0
      first
      | (have j0 := f337180_13 X0
         grind)
      | (have r₁ := f337180_13 X0
         have r₂ := f337180_22
         grind)
      | exact resolve f337180_13 f337180_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f337180_47 : (M.op x y) = (M.op x (M.op y (τ (σ x)))) := by
      first
      | (have i₁ := f337180_12 (M.op (σ y) (σ y))
         have i₂ := f337180_23 (σ y)
         grind)
      | exact superpose f337180_23 f337180_12
      | exact resolve f337180_12 f337180_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f337180_48 : False := by
      first
      | (have r₁ := f337180_47
         have r₂ := f337180_21
         grind)
      | exact resolve f337180_47 f337180_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f337180_48
  clear eq12605
  have eq337192 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (τ (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq319984 eq13115
    | exact resolve eq13115 eq319984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13115 eq319984
  have eq337643 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq337192
    | exact resolve eq337192 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337192
  have eq337651 : (M.op x y) = (M.op x (M.op y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq337180
    | exact resolve eq337180 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq337180
  have eq337966 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq337643
       have i₂ := eq137529 sF4 sF3
       grind)
    | exact superpose eq137529 eq337643
    | exact resolve eq337643 eq137529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337643
  have eq337971 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq337651
       have i₂ := eq3991 x
       grind)
    | exact superpose eq3991 eq337651
    | exact resolve eq337651 eq3991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991 eq337651
  have eq340355 : (σ x) = (M.op (M.op (σ y) x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq322472 eq337966
    | exact resolve eq337966 eq322472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322472 eq337966
  have eq340659 : (σ x) = (M.op (M.op (σ y) x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq340355
  have eq354413 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq340659 eq1294
    | exact resolve eq1294 eq340659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340659
  have eq356870 : (M.op x x) = (τ (M.op (σ x) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq354413 eq72
    | exact resolve eq72 eq354413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354413
  have eq388278 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) x) (M.op (σ x) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq356870 eq314
    | exact resolve eq314 eq356870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356870
  have eq388319 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1282 eq388278
    | exact resolve eq388278 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388278
  have eq388329 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op (M.op x x) (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq388319
       have i₂ := eq30700 (M.op x x)
       grind)
    | exact superpose eq30700 eq388319
    | exact resolve eq388319 eq30700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388319
  have eq388334 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq388329
       have i₂ := eq113414 sF0 sF0 x
       grind)
    | exact superpose eq113414 eq388329
    | exact resolve eq388329 eq113414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388329
  have eq388335 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq140 eq388334
    | exact resolve eq388334 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388334
  have eq388353 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq388335 eq320299
    | exact resolve eq320299 eq388335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320299 eq388335
  have eq388668 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq388353
  have eq391480 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq388668 eq147
    | exact resolve eq147 eq388668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq388668
  have eq392033 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq181 eq391480
    | exact resolve eq391480 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq391480
  have eq396999 : (M.op x (M.op x y)) = (M.op (M.op (M.op y y) (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq392033 eq19961
    | exact resolve eq19961 eq392033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19961 eq392033
  have eq397518 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53 eq396999
    | exact resolve eq396999 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq396999
  have eq397838 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq397518 eq337971
    | exact resolve eq337971 eq397518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337971 eq397518
  have eq398113 : y = (M.op x y) := by grind
  clear eq397838
  have eq399570 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq398113 eq20
    | exact resolve eq20 eq398113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq399686 : x = (M.op (M.op y x) y) := by
    first
    | exact superpose eq398113 eq2368
    | exact resolve eq2368 eq398113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2368
  have eq399899 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq399570
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq399570
    | exact resolve eq399570 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq399570
  have eq422168 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq3439 X0 X1
       have i₂ := eq25944 X0 (M.op X1 y) X1
       grind)
    | (have i₁ := eq3439 X0 X1
       have i₂ := eq25944 X0 X1 (M.op X1 y)
       grind)
    | exact superpose eq25944 eq3439
    | exact resolve eq3439 eq25944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439 eq25944
  have eq422169 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq422168 X0 X1
       have i₂ := eq137529 X0 sF0
       grind)
    | exact superpose eq137529 eq422168
    | exact resolve eq422168 eq137529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137529 eq422168
  have eq422170 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq398113 eq422169
    | exact resolve eq422169 eq398113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422169
  have eq422946 : (M.op x y) = (M.op x (M.op y (σ (M.op (M.op y x) y)))) := by
    first
    | (have i₁ := eq12604 (M.op y y)
       have i₂ := eq422170 y y
       grind)
    | exact superpose eq422170 eq12604
    | exact resolve eq12604 eq422170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12604
  have eq422949 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op (M.op y x) y)))) := by
    first
    | (have i₁ := eq12699 (M.op y y)
       have i₂ := eq422170 y y
       grind)
    | exact superpose eq422170 eq12699
    | exact resolve eq12699 eq422170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12699 eq422170
  have eq423466 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq422949
       have i₂ := eq399686
       grind)
    | exact superpose eq399686 eq422949
    | exact resolve eq422949 eq399686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422949
  have eq423469 : (M.op x y) = (M.op x (M.op y (σ x))) := by
    first
    | (have i₁ := eq422946
       have i₂ := eq399686
       grind)
    | exact superpose eq399686 eq422946
    | exact resolve eq422946 eq399686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399686 eq422946
  have eq424251 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq423466
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq423466
    | exact resolve eq423466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423466
  have eq424254 : (M.op x y) = (M.op x (M.op y (σ x))) := by
    first
    | (have i₁ := eq423469
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq423469
    | exact resolve eq423469 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq423469
  have eq424824 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4268 eq424251
    | exact resolve eq424251 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4268 eq424251
  have eq424826 : y = (M.op x (M.op y (σ x))) := by
    first
    | exact superpose eq398113 eq424254
    | exact resolve eq424254 eq398113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398113 eq424254
  have eq425768 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq424824 eq13136
    | exact resolve eq13136 eq424824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13136 eq424824
  have eq426237 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq399899 eq425768
    | exact resolve eq425768 eq399899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399899 eq425768
  have eq426801 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op y (σ x)) y)) := by
    intro X0
    first
    | exact superpose eq424826 eq1293
    | exact resolve eq1293 eq424826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293 eq424826
  have eq426881 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq426801 X0
       have i₂ := eq1294 X0 sF2 y
       grind)
    | exact superpose eq1294 eq426801
    | exact resolve eq426801 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq426801
  have eq437044 : (M.op x x) = (τ (M.op (σ x) x)) := by
    first
    | exact superpose eq426881 eq72
    | exact resolve eq72 eq426881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq426881
  have eq459096 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) x) (M.op (σ x) x)) := by
    first
    | exact superpose eq437044 eq314
    | exact resolve eq314 eq437044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq437044
  have eq459161 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq1282 eq459096
    | exact resolve eq459096 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq459096
  have eq459179 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x y) (M.op (M.op x x) (M.op x y)))) := by
    first
    | (have i₁ := eq459161
       have i₂ := eq30700 (M.op x x)
       grind)
    | exact superpose eq30700 eq459161
    | exact resolve eq459161 eq30700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30700 eq459161
  have eq459190 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq459179
       have i₂ := eq113414 sF0 sF0 x
       grind)
    | exact superpose eq113414 eq459179
    | exact resolve eq459179 eq113414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113414 eq459179
  have eq459200 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq426237 eq459190
    | exact resolve eq459190 eq426237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426237 eq459190
  have eq459205 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq140 eq459200
    | exact resolve eq459200 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq459200
  have eq459467 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ x))) (σ (M.op x y))) := by
    first
    | exact superpose eq459205 eq33349
    | exact resolve eq33349 eq459205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33349 eq459205
  have eq459533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq459467
       have i₂ := eq25310 sF1 sF1 sF2
       grind)
    | exact superpose eq25310 eq459467
    | exact resolve eq459467 eq25310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25310 eq459467
  have eq459796 : False := by grind
  exact eq459796

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_pyx_pyy_pxy_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
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
  have eq65 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
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
  have eq93 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ x)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
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
  have eq112 : x ≠ x ∨ (k (M.op (M.op x y) (M.op x y)) x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq78 eq12
    | (have j0 := eq12 (M.op (M.op x y) (M.op x y)) x
       grind)
    | (have r₁ := eq12 (M.op (M.op x y) (M.op x y)) x
       have r₂ := eq78
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq115 : (σ x) ≠ (σ x) ∨ (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq93 eq12
    | (have j0 := eq12 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)
       have r₂ := eq93
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by grind
  clear eq115
  have eq118 : (k (M.op (M.op x y) (M.op x y)) x) = (M.op x (M.op (M.op x y) (M.op x y))) := by grind
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
    | (have r₁ := eq125 x
       have r₂ := eq12 x x
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
  have eq356 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq65
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq357 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq356
    | exact resolve eq356 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq359 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq357
    | exact resolve eq357 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq361 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq359
    | exact resolve eq359 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq363 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) (M.op X5 X4)) X5) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X4 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X2 X3) X4 X5
       have i₂ := eq53 X0 X3 X2 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq392 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op (M.op X3 X4) X2)) X5) (M.op X4 X5)) = (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X0 (M.op (M.op X3 X4) X2)) X5 X4 X3
       have i₂ := eq53 X0 X1 X2 (M.op X3 X4)
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
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
  have eq411 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op X4 X2))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X3 X4 (M.op X0 (M.op X4 X2))
       have i₂ := eq53 X0 X1 X2 X4
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
  have eq483 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) y) = X0 := by
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
  have eq504 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq399
    | (have j0 := eq399 X0 (σ x) (σ y)
       grind)
    | exact resolve eq399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = (M.op (M.op X0 X2) X3) := by
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
  have eq510 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X0 X1) y)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq399
    | exact resolve eq399 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (σ y))) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq399
    | exact resolve eq399 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
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
  have eq526 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y (M.op x y))) := by
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
  have eq527 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
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
  have eq535 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op X1 y)) X1) := by
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
  have eq536 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op X1 y)) X1)) := by
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
  have eq537 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op X1 (σ y))) X1)) := by
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
  have eq538 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (M.op X1 (σ y))) X1) := by
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
  have eq540 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq538 eq537
    | (have j0 := eq537 X0 (σ x)
       grind)
    | exact resolve eq537 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq538
  have eq542 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq536 X0 x
       have i₂ := eq535 X0 x
       grind)
    | (have i₁ := eq536 X0 x
       have i₂ := eq535 X0 x
       grind)
    | exact superpose eq535 eq536
    | (have j0 := eq536 X0 x
       grind)
    | exact resolve eq536 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq553 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) = (M.op (M.op X3 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq370 X0 X1 X2 X3 X4 x
       have i₂ := eq508 X3 x X0 X4
       grind)
    | exact superpose eq508 eq370
    | exact resolve eq370 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq563 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq483 (M.op X0 (M.op sF0 x))
       have i₂ := eq399 X0 sF0 x
       grind)
    | exact superpose eq399 eq483
    | exact resolve eq483 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq571 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) (M.op y y)) X1)) = (M.op (M.op X0 x) y) := by
    intro X0 X1
    first
    | exact superpose eq563 eq379
    | exact resolve eq379 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq563
  have eq604 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq526 eq399
    | exact resolve eq399 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq527 eq399
    | exact resolve eq399 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq803 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op (M.op X4 X5) (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X5))) := by
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
  have eq825 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3))) := by
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
  have eq827 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) (M.op (M.op X2 X1) X3))) := by
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
  have eq910 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
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
  have eq911 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X3)) := by
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
  have eq912 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op (M.op X1 X4) X3)) := by
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
  have eq920 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X5 X4)) X5) := by
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
  have eq921 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X5 (M.op (M.op X0 X4) X2))) X5) := by
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
  have eq924 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X0 X4)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq921 X0 X1 X2 X3 X4 x
       have i₂ := eq508 X1 x (M.op X0 X4) X2
       grind)
    | exact superpose eq508 eq921
    | exact resolve eq921 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq1060 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) (M.op (M.op (M.op x y) (M.op y y)) X0)) := by
    intro X0
    first
    | exact superpose eq80 eq409
    | exact resolve eq409 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1149 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X4 X3)) X4) := by
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
  have eq1151 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op (M.op X3 X4) (M.op (M.op X1 X2) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op (M.op X0 X1) X2) (M.op X1 X2) X4
       have i₂ := eq409 X0 X1 X2
       grind)
    | exact superpose eq409 eq55
    | exact resolve eq55 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1163 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op X0 (M.op X4 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq920 X0 X1 X2 X3 X4 x
       have i₂ := eq1149 X0 X1 X2 X4 x
       grind)
    | exact superpose eq1149 eq920
    | exact resolve eq920 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1198 : (M.op (M.op x y) x) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq571 eq1060
    | exact resolve eq1060 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq1060
  have eq1221 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 (M.op (M.op x y) x)) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 y (M.op x x)
       have i₂ := eq1198
       grind)
    | exact superpose eq1198 eq53
    | exact resolve eq53 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1225 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) x)) (M.op x x)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq399 X0 (M.op x x) y
       have i₂ := eq1198
       grind)
    | exact superpose eq1198 eq399
    | exact resolve eq399 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1229 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1225 X0
       have i₂ := eq911 X0 x sF0 x
       grind)
    | exact superpose eq911 eq1225
    | exact resolve eq1225 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1233 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1221 X0 X1
       have i₂ := eq911 X0 x sF0 x
       grind)
    | exact superpose eq911 eq1221
    | exact resolve eq1221 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq1221
  have eq1290 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op x y))) := by
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
  have eq1293 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1229 eq54
    | exact resolve eq54 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1229
  have eq1309 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) X1) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1293 eq535
    | exact resolve eq535 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq1310 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1293 eq542
    | exact resolve eq542 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq1323 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq1293 eq88
    | exact resolve eq88 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1293
  have eq1654 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op x (M.op y X1))) := by
    intro X0 X1
    first
    | exact superpose eq407 eq910
    | exact resolve eq910 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1655 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq408 eq910
    | exact resolve eq910 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1659 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq910 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq409 X0 X2 X3
       grind)
    | exact superpose eq409 eq910
    | exact resolve eq910 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1660 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X3 X2))) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq910 X1 (M.op (M.op X0 X2) (M.op X3 X2)) X3
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq910
    | exact resolve eq910 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1667 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq101 eq910
    | exact resolve eq910 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1669 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (σ y))) = (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq504 eq910
    | exact resolve eq910 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq1674 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq93 eq910
    | exact resolve eq910 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1677 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq910 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq399 X0 X2 X2
       grind)
    | exact superpose eq399 eq910
    | exact resolve eq910 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1710 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op X2 X1)
       have i₂ := eq910 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq910 eq9
    | exact resolve eq9 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1764 : (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1674 eq117
    | exact resolve eq117 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1674
  have eq1785 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1669 eq540
    | exact resolve eq540 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq1669
  have eq1787 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1667 X0
       have i₂ := eq1677 sF4 sF2 sF3
       grind)
    | exact superpose eq1677 eq1667
    | exact resolve eq1667 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1808 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq825 X0 X1 X2 x
       have i₂ := eq1660 X2 X0 x X1
       grind)
    | exact superpose eq1660 eq825
    | exact resolve eq825 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1812 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 (M.op X0 X4)) X2) = (M.op (M.op X1 (M.op X2 X4)) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq924 X2 X1 X0 x X4
       have i₂ := eq1660 X0 X1 x X4
       grind)
    | exact superpose eq1660 eq924
    | exact resolve eq924 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1814 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1163 X0 X2 X1 x X4
       have i₂ := eq1660 X1 X4 x X2
       grind)
    | exact superpose eq1660 eq1163
    | exact resolve eq1163 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1815 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq827 X0 X1 X2 x
       have i₂ := eq1660 X2 X0 x (M.op X2 X1)
       grind)
    | exact superpose eq1660 eq827
    | exact resolve eq827 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq1817 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X0 X2)) (M.op X0 (M.op X4 X2))) = X3 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq411 X0 x X2 X3 X4
       have i₂ := eq1660 X0 (M.op X3 X4) x X2
       grind)
    | exact superpose eq1660 eq411
    | exact resolve eq411 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq1821 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq803 X0 X1 X2 X3 X4 x
       have i₂ := eq1660 X4 (M.op X0 X4) x (M.op (M.op X2 X3) (M.op X1 X3))
       grind)
    | exact superpose eq1660 eq803
    | exact resolve eq803 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq1822 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op X3 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1151 X0 X1 X2 X3 x
       have i₂ := eq1660 X3 (M.op X0 X3) x (M.op X1 X2)
       grind)
    | exact superpose eq1660 eq1151
    | exact resolve eq1151 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1840 : ∀ X0 X2 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) (M.op X0 (M.op (σ y) X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq416 X0 X2 x
       have i₂ := eq1660 X0 sF4 X2 x
       grind)
    | exact superpose eq1660 eq416
    | exact resolve eq416 eq1660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq1660
  have eq1845 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op X3 (M.op X4 X2))) X5) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq392 X0 X1 X2 X3 X4 X5
       have i₂ := eq1659 X3 X0 X4 X2
       grind)
    | exact superpose eq1659 eq392
    | exact resolve eq392 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq1901 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq553 X0 X1 X2 X3 X4
       have i₂ := eq1659 X0 (M.op X3 (M.op X2 X4)) (M.op X1 X2) X1
       grind)
    | exact superpose eq1659 eq553
    | exact resolve eq553 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq1920 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op X1 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq912 X0 X1 X2 X3 X4
       have i₂ := eq1659 X1 (M.op (M.op (M.op X0 X1) X2) X3) X4 X3
       grind)
    | exact superpose eq1659 eq912
    | exact resolve eq912 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq1922 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) X0) (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq393 x
       have i₂ := eq1659 y (M.op (M.op sF0 x) x) y x
       grind)
    | exact superpose eq1659 eq393
    | exact resolve eq393 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1926 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1310 X0
       have i₂ := eq1659 X0 (M.op sF0 X0) x sF0
       grind)
    | exact superpose eq1659 eq1310
    | exact resolve eq1310 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1929 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 x
       have i₂ := eq1659 X0 sF0 x y
       grind)
    | exact superpose eq1659 eq510
    | exact resolve eq510 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq1932 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 x
       have i₂ := eq1659 X0 sF4 x sF3
       grind)
    | exact superpose eq1659 eq511
    | exact resolve eq511 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq1984 : (k (M.op (M.op x y) (M.op x y)) x) = (M.op x (M.op x (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1654 eq118
    | exact resolve eq118 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq2013 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) := by
    intro X0
    first
    | exact superpose eq1655 eq1787
    | exact resolve eq1787 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq2032 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op X2 (M.op X3 (M.op X1 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1821 X0 X1 X2 X3 X4
       have i₂ := eq1659 X2 X4 X3 (M.op X1 X3)
       grind)
    | exact superpose eq1659 eq1821
    | exact resolve eq1821 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq2052 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq1323
       have i₂ := eq1929 x sF0
       grind)
    | exact superpose eq1929 eq1323
    | exact resolve eq1323 eq1929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323 eq1929
  have eq2055 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1290 eq1926
    | exact resolve eq1926 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926
  have eq2057 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1922 x
       have i₂ := eq1815 (M.op (M.op sF0 x) x) x y
       grind)
    | exact superpose eq1815 eq1922
    | exact resolve eq1922 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq2072 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1901 X0 X1 X2 X3 X4
       have i₂ := eq1814 (M.op X3 (M.op X2 X4)) (M.op X1 X2) X1 X0
       grind)
    | (have i₁ := eq1901 X0 X1 X2 X3 X4
       have i₂ := eq1814 (M.op X3 (M.op X2 X4)) X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq1814 eq1901
    | exact resolve eq1901 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq2135 : (k (M.op (M.op x y) (M.op x y)) x) = (M.op x (M.op x x)) := by
    first
    | exact superpose eq526 eq1984
    | exact resolve eq1984 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984
  have eq2165 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2013 X0
       have i₂ := eq525 X0 sF2 sF3
       grind)
    | exact superpose eq525 eq2013
    | exact resolve eq2013 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2176 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2032 X0 X1 X2 x X4
       have i₂ := eq525 X2 x X1
       grind)
    | exact superpose eq525 eq2032
    | exact resolve eq2032 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2186 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq2052
       have i₂ := eq1814 sF0 sF0 y x
       grind)
    | (have i₁ := eq2052
       have i₂ := eq1814 sF0 y sF0 x
       grind)
    | exact superpose eq1814 eq2052
    | exact resolve eq2052 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2201 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2072 X0 x X2 X3 X4
       have i₂ := eq1815 X0 X2 x
       grind)
    | exact superpose eq1815 eq2072
    | exact resolve eq2072 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2253 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq526 eq2186
    | exact resolve eq2186 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq2186
  have eq2336 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1785 eq53
    | exact resolve eq53 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2342 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) X1))) X2) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1785 eq53
    | exact resolve eq53 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2351 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2342 X0 x X1
       have i₂ := eq508 X0 X1 sF4 x
       grind)
    | exact superpose eq508 eq2342
    | exact resolve eq2342 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2383 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X0) X1) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq2055 eq53
    | exact resolve eq53 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2389 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op x y) X1))) X2) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq2055 eq53
    | exact resolve eq53 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2398 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2389 X0 x X1
       have i₂ := eq508 X0 X1 sF0 x
       grind)
    | exact superpose eq508 eq2389
    | exact resolve eq2389 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2465 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq2165 eq399
    | exact resolve eq399 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2565 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2465 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq399 X0 X1 sF3
       grind)
    | exact superpose eq399 eq2465
    | exact resolve eq2465 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2566 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ y) X1)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2465 (M.op (M.op X0 X1) (M.op sF3 X1))
       have i₂ := eq9 X0 X1 sF3
       grind)
    | exact superpose eq9 eq2465
    | exact resolve eq2465 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465
  have eq2664 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op (M.op (M.op X0 X2) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1815 X1 (M.op X2 X3) (M.op (M.op X0 X2) X3)
       have i₂ := eq409 X0 X2 X3
       grind)
    | exact superpose eq409 eq1815
    | exact resolve eq1815 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2703 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq407 (M.op y x)
       have i₂ := eq1815 (M.op sF0 (M.op y x)) x y
       grind)
    | exact superpose eq1815 eq407
    | exact resolve eq407 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq2704 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq408 (M.op sF3 x)
       have i₂ := eq1815 (M.op sF4 (M.op sF3 x)) x sF3
       grind)
    | exact superpose eq1815 eq408
    | exact resolve eq408 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2750 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op (M.op X0 X2) (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2664 X0 X1 X2 X3
       have i₂ := eq1659 (M.op X0 X2) X1 X3 X0
       grind)
    | exact superpose eq1659 eq2664
    | exact resolve eq2664 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq2778 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op X0 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2750 X0 X1 X2 X3
       have i₂ := eq1659 X0 X1 X2 (M.op X3 X0)
       grind)
    | exact superpose eq1659 eq2750
    | exact resolve eq2750 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq2831 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2703 eq399
    | exact resolve eq399 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2926 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2704 eq399
    | exact resolve eq399 eq2704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704
  have eq2947 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2926 eq1932
    | exact resolve eq1932 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq3172 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op y y) X1)) = (M.op (M.op X0 (M.op (M.op x y) (M.op x x))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq2253 eq53
    | exact resolve eq53 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq3181 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op (M.op y y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3172 X0 X1
       have i₂ := eq508 X0 sF0 x x
       grind)
    | exact superpose eq508 eq3172
    | exact resolve eq3172 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq3172
  have eq3192 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op y (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3181 X0 X1
       have i₂ := eq1659 y (M.op X0 X1) y X1
       grind)
    | exact superpose eq1659 eq3181
    | exact resolve eq3181 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3181
  have eq3199 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3192 X0 X1
       have i₂ := eq1815 (M.op X0 X1) X1 y
       grind)
    | exact superpose eq1815 eq3192
    | exact resolve eq3192 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq3229 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq525 X1 (M.op X2 X3) (M.op (M.op X0 X2) X3)
       have i₂ := eq409 X0 X2 X3
       grind)
    | exact superpose eq409 eq525
    | exact resolve eq525 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3232 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq525 X3 X4 (M.op X0 (M.op X4 X2))
       have i₂ := eq53 X0 X1 X2 X4
       grind)
    | exact superpose eq53 eq525
    | exact resolve eq525 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3236 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) y)) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq604 eq525
    | exact resolve eq525 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3237 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (σ x)) (σ y))) = (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq647 eq525
    | exact resolve eq525 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3337 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (σ x)) (σ y))) = (M.op X1 (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq1655 eq3237
    | exact resolve eq3237 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3237
  have eq3338 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 x) y)) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | exact superpose eq1654 eq3236
    | exact resolve eq3236 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236
  have eq3342 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3232 X0 X1 X2 X3 X4
       have i₂ := eq1659 X0 X4 X1 (M.op X2 X1)
       grind)
    | exact superpose eq1659 eq3232
    | exact resolve eq3232 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232
  have eq3345 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3229 X0 X1 X2 X3
       have i₂ := eq1659 X2 X1 X3 X0
       grind)
    | exact superpose eq1659 eq3229
    | exact resolve eq3229 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3368 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3337 X0 X1
       have i₂ := eq1659 X0 X1 sF2 sF3
       grind)
    | exact superpose eq1659 eq3337
    | exact resolve eq3337 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337
  have eq3369 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3338 X0 X1
       have i₂ := eq1659 X0 X1 x y
       grind)
    | exact superpose eq1659 eq3338
    | exact resolve eq3338 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3372 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3342 X0 x X2 X3 X4
       have i₂ := eq525 X0 x X2
       grind)
    | exact superpose eq525 eq3342
    | exact resolve eq3342 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3375 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 X3))) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3345 X0 X1 X2 X3
       have i₂ := eq1659 X0 X1 X2 X3
       grind)
    | exact superpose eq1659 eq3345
    | exact resolve eq3345 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3390 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ x) (M.op (σ y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq3368
    | (have j0 := eq3368 X0 X1
       grind)
    | exact resolve eq3368 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3368
  have eq3391 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x (M.op y X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3369 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3369
    | (have j0 := eq3369 X0 X1
       grind)
    | exact resolve eq3369 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369
  have eq3465 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1815 X1 (M.op X2 X2) X0
       have i₂ := eq1677 X0 X0 X2
       grind)
    | exact superpose eq1677 eq1815
    | exact resolve eq1815 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3467 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq399 X0 X1 (M.op X2 X2)
       have i₂ := eq1677 X1 X0 X2
       grind)
    | exact superpose eq1677 eq399
    | exact resolve eq399 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3468 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X2 (M.op X3 X3) X1
       have i₂ := eq1677 X1 X0 X3
       grind)
    | exact superpose eq1677 eq53
    | exact resolve eq53 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3487 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq409 X0 X1 (M.op X2 X2)
       have i₂ := eq1677 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X2
       grind)
    | exact superpose eq1677 eq409
    | exact resolve eq409 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3499 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2703 (M.op x x)
       have i₂ := eq1677 y sF0 x
       grind)
    | exact superpose eq1677 eq2703
    | exact resolve eq2703 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq3535 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3468 X0 X1 X2 X3
       have i₂ := eq1659 X3 (M.op X0 X2) X3 X2
       grind)
    | exact superpose eq1659 eq3468
    | exact resolve eq3468 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq3569 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3535 X0 X1 X2 x
       have i₂ := eq1815 (M.op X0 X2) X2 x
       grind)
    | exact superpose eq1815 eq3535
    | exact resolve eq3535 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535
  have eq3816 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X1 X0) (M.op (M.op X0 X2) (M.op (σ x) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X0 (M.op (M.op X0 X1) (M.op sF2 X1))
       have i₂ := eq9 X0 X1 sF2
       grind)
    | exact superpose eq9 eq95
    | exact resolve eq95 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3902 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op (σ x) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3816 X0 X1 X2
       have i₂ := eq1659 X0 (M.op X1 X0) X2 (M.op sF2 X2)
       grind)
    | exact superpose eq1659 eq3816
    | exact resolve eq3816 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq3936 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X1 X0) (M.op X0 (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq3902 X0 X1 X1
       have i₂ := eq525 X0 X1 sF2
       grind)
    | exact superpose eq525 eq3902
    | exact resolve eq3902 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3902
  have eq4044 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op (M.op x y) y) X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq3499 eq53
    | exact resolve eq53 eq3499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3499
  have eq4452 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 X1) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq604 eq1710
    | exact resolve eq1710 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4455 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 X1) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq647 eq1710
    | exact resolve eq1710 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4524 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq399 (M.op (M.op X0 X2) X1) X1 X2
       have i₂ := eq1710 X0 X2 X1
       grind)
    | exact superpose eq1710 eq399
    | exact resolve eq399 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq4575 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) (M.op X5 X4)) X5) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X4 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq363 X0 X1 X2 X3 X4 X5
       have i₂ := eq4524 X0 (M.op X1 X2) X1
       grind)
    | (have i₁ := eq363 X0 X1 X2 X3 X4 X5
       have i₂ := eq4524 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq4524 eq363
    | exact resolve eq363 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq4590 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1309 X0 X1
       have i₂ := eq4524 X0 (M.op X1 y) X1
       grind)
    | (have i₁ := eq1309 X0 X1
       have i₂ := eq4524 X0 X1 (M.op X1 y)
       grind)
    | exact superpose eq4524 eq1309
    | exact resolve eq1309 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq4593 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2565 X0 x
       have i₂ := eq4524 X0 (M.op x sF3) x
       grind)
    | (have i₁ := eq2565 X0 X1
       have i₂ := eq4524 X0 X1 (M.op X1 sF3)
       grind)
    | exact superpose eq4524 eq2565
    | exact resolve eq2565 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq4607 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1149 X0 X1 X2 X3 X4
       have i₂ := eq4524 (M.op (M.op X0 X1) X2) (M.op X4 X3) X4
       grind)
    | (have i₁ := eq1149 X0 X1 X2 X3 X4
       have i₂ := eq4524 (M.op (M.op X0 X1) X2) X4 (M.op X4 X3)
       grind)
    | exact superpose eq4524 eq1149
    | exact resolve eq1149 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq4624 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 x) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2398 X0 X1
       have i₂ := eq4524 X0 (M.op X1 y) x
       grind)
    | (have i₁ := eq2398 X0 X1
       have i₂ := eq4524 X0 x (M.op X1 y)
       grind)
    | exact superpose eq4524 eq2398
    | exact resolve eq2398 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq4643 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2351 X0 X1
       have i₂ := eq4524 X0 (M.op X1 sF3) sF2
       grind)
    | (have i₁ := eq2351 X0 X1
       have i₂ := eq4524 X0 sF2 (M.op X1 sF3)
       grind)
    | exact superpose eq4524 eq2351
    | exact resolve eq2351 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351
  have eq4775 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X4 (M.op X2 X3))) = (M.op (M.op (M.op X0 X3) X5) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4575 X0 X1 X2 X3 X4 X5
       have i₂ := eq4524 (M.op X0 X3) (M.op X5 X4) X5
       grind)
    | (have i₁ := eq4575 X0 X1 X2 X3 X4 X5
       have i₂ := eq4524 (M.op X0 X3) X5 (M.op X5 X4)
       grind)
    | exact superpose eq4524 eq4575
    | exact resolve eq4575 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4575
  have eq4912 : (k (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (σ x))) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq1764 eq204
    | exact resolve eq204 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq1764
  have eq4913 : (τ (M.op (σ x) (M.op (σ x) (σ x)))) = (k (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) x) := by
    first
    | exact superpose eq38 eq4912
    | exact resolve eq4912 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4912
  have eq4917 : (τ (M.op (σ x) (M.op (σ x) (σ x)))) = (k (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) x) := by
    first
    | (have i₁ := eq4913
       have i₂ := eq236 sF4
       grind)
    | exact superpose eq236 eq4913
    | exact resolve eq4913 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913
  have eq5501 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) X0) X0) x) := by
    intro X0
    first
    | (have i₁ := eq2057 x
       have i₂ := eq3199 sF0 x
       grind)
    | (have i₁ := eq2057 x
       have i₂ := eq3199 sF0 x
       grind)
    | exact superpose eq3199 eq2057
    | exact resolve eq2057 eq3199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq6691 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X1)) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3467 (M.op (M.op X0 X1) X2) (M.op X2 X1) X3
       have i₂ := eq1710 X0 X1 X2
       grind)
    | exact superpose eq1710 eq3467
    | exact resolve eq3467 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6696 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 (M.op x y)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq604 eq3467
    | exact resolve eq3467 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7493 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq1785 eq3569
    | exact resolve eq3569 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7494 : ∀ X0 X1 : G, (M.op x (M.op X0 y)) = (M.op (M.op (M.op (M.op x y) X0) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq2055 eq3569
    | exact resolve eq3569 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7499 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) x) X1) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3569 (M.op X0 X1) X2 X1
       have i₂ := eq3199 X0 X1
       grind)
    | (have i₁ := eq3569 (M.op X0 x) X1 x
       have i₂ := eq3199 X0 X1
       grind)
    | exact superpose eq3199 eq3569
    | exact resolve eq3569 eq3199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3199
  have eq8031 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq408 eq4524
    | exact resolve eq4524 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq8032 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1785 eq4524
    | exact resolve eq4524 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8039 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 X2) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4524 (M.op X0 X2) X3 X1
       have i₂ := eq4524 X0 X2 X1
       grind)
    | (have i₁ := eq4524 (M.op X0 X2) X3 X1
       have i₂ := eq4524 X0 X1 X2
       grind)
    | exact superpose eq4524 eq4524
    | exact resolve eq4524 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8047 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 x) y) X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq604 eq4524
    | exact resolve eq4524 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq8051 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 (σ x)) (σ y)) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq647 eq4524
    | exact resolve eq4524 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq8118 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X2)) = (M.op X3 (M.op X1 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq525 X3 X1 (M.op X0 X2)
       have i₂ := eq4524 X0 X2 X1
       grind)
    | (have i₁ := eq525 X3 X1 (M.op X0 X2)
       have i₂ := eq4524 X0 X1 X2
       grind)
    | exact superpose eq4524 eq525
    | exact resolve eq525 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8134 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op X0 X3) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1808 (M.op X0 X3) X1 X2
       have i₂ := eq4524 X0 X3 (M.op X1 X2)
       grind)
    | (have i₁ := eq1808 (M.op X0 X3) X1 X2
       have i₂ := eq4524 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq4524 eq1808
    | exact resolve eq1808 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8170 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X2)) = (M.op X3 (M.op X1 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8118 X0 X1 X2 X3
       have i₂ := eq1659 X0 X1 X1 X2
       grind)
    | exact superpose eq1659 eq8118
    | exact resolve eq8118 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8118
  have eq8302 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) X0) x) X0) := by
    intro X0
    first
    | exact superpose eq5501 eq4524
    | exact resolve eq4524 eq5501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5501
  have eq9846 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) = (M.op X0 (M.op (M.op X1 (M.op (σ y) X2)) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1840 eq525
    | exact resolve eq525 eq1840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq9871 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) = (M.op X0 (M.op X1 (M.op (M.op (σ y) X2) (σ x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9846 X1 X0 X2
       have i₂ := eq1659 X0 X1 (M.op sF3 X2) sF2
       grind)
    | exact superpose eq1659 eq9846
    | exact resolve eq9846 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9846
  have eq9986 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) = (M.op X0 (M.op X1 (M.op (σ x) (M.op (σ y) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9871 X0 x X2
       have i₂ := eq1814 X0 (M.op sF3 X2) sF2 x
       grind)
    | (have i₁ := eq9871 X0 x X2
       have i₂ := eq1814 X0 sF2 (M.op sF3 X2) x
       grind)
    | exact superpose eq1814 eq9871
    | exact resolve eq9871 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9871
  have eq10070 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (σ x) (M.op (σ y) X2)))) = (M.op X0 (M.op (σ x) (M.op (σ y) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1655 eq9986
    | exact resolve eq9986 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9986
  have eq12985 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) X2) (M.op X1 (σ x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3936 X1 (M.op X0 X2)
       have i₂ := eq4524 X0 X2 X1
       grind)
    | (have i₁ := eq3936 X1 (M.op X0 X2)
       have i₂ := eq4524 X0 X1 X2
       grind)
    | exact superpose eq4524 eq3936
    | exact resolve eq3936 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13010 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (M.op (M.op x y) (σ x)) x)) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq8302 eq3936
    | exact resolve eq3936 eq8302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8302
  have eq13038 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 (σ x))) (M.op X2 X2)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3936 eq3487
    | exact resolve eq3487 eq3936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq13092 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) (M.op X1 (σ x))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13038 X0 X1 X2
       have i₂ := eq8039 (M.op X0 X1) (M.op X1 sF2) (M.op X2 X2) sF4
       grind)
    | (have i₁ := eq13038 X0 X1 X2
       have i₂ := eq8039 (M.op X0 X1) sF4 (M.op X1 sF2) (M.op X2 X2)
       grind)
    | exact superpose eq8039 eq13038
    | exact resolve eq13038 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13038
  have eq13114 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (M.op x (M.op x y)) x)) (M.op (M.op x y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq13010 x
       have i₂ := eq1812 (M.op sF0 sF2) x (M.op x sF0) x
       grind)
    | (have i₁ := eq13010 x
       have i₂ := eq1812 (M.op x sF0) x (M.op sF0 sF2) x
       grind)
    | exact superpose eq1812 eq13010
    | exact resolve eq13010 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13010
  have eq13189 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) (σ x)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13092 X0 x x
       have i₂ := eq6691 (M.op (M.op X0 x) sF4) sF2 x x
       grind)
    | exact superpose eq6691 eq13092
    | exact resolve eq13092 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13092
  have eq13206 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (M.op x y) (σ x))) (M.op x (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq13114 X0
       have i₂ := eq8134 X0 (M.op x sF0) x (M.op sF0 sF2)
       grind)
    | (have i₁ := eq13114 X0
       have i₂ := eq8134 X0 sF2 sF0 (M.op (M.op x sF0) x)
       grind)
    | exact superpose eq8134 eq13114
    | exact resolve eq13114 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13114
  have eq13260 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (M.op X0 X1) (σ x)) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq13189 X0 x
       have i₂ := eq8039 (M.op X0 x) sF4 sF2 x
       grind)
    | (have i₁ := eq13189 X0 X1
       have i₂ := eq8039 (M.op X0 X1) X1 sF4 sF2
       grind)
    | exact superpose eq8039 eq13189
    | exact resolve eq13189 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13189
  have eq13275 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq13206 X0
       have i₂ := eq8134 X0 sF0 sF2 (M.op x (M.op x sF0))
       grind)
    | (have i₁ := eq13206 X0
       have i₂ := eq8134 X0 (M.op x sF0) x (M.op sF0 sF2)
       grind)
    | exact superpose eq8134 eq13206
    | exact resolve eq13206 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13206
  have eq13322 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op (M.op x y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq13275 X0
       have i₂ := eq1808 (M.op X0 (M.op x (M.op x sF0))) sF2 sF0
       grind)
    | (have i₁ := eq13275 X0
       have i₂ := eq1808 (M.op X0 (M.op x (M.op x sF0))) sF0 sF2
       grind)
    | exact superpose eq1808 eq13275
    | exact resolve eq13275 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13275
  have eq13351 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x (M.op x (M.op x y)))) (M.op x (M.op y (σ x)))) := by
    intro X0
    first
    | exact superpose eq1654 eq13322
    | exact resolve eq13322 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13322
  have eq13365 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op x (M.op y (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq13351 X0
       have i₂ := eq1815 X0 sF0 x
       grind)
    | exact superpose eq1815 eq13351
    | exact resolve eq13351 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13351
  have eq13403 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 (σ x))) = (M.op (M.op (M.op X0 X2) (M.op x y)) (M.op x (M.op y (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq13365 eq12985
    | exact resolve eq12985 eq13365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12985 eq13365
  have eq13423 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 (σ x))) = (M.op (M.op (M.op X0 X2) x) (M.op (M.op x (M.op y (σ x))) y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq4624 eq13403
    | exact resolve eq13403 eq4624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13403
  have eq13441 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 (σ x))) = (M.op (M.op (M.op X0 X2) x) (M.op x (M.op (M.op y (σ x)) y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13423 X0 X1 X2
       have i₂ := eq1659 x (M.op (M.op X0 X2) x) (M.op y sF2) y
       grind)
    | exact superpose eq1659 eq13423
    | exact resolve eq13423 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13423
  have eq13456 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 (σ x))) = (M.op (M.op (M.op X0 X2) x) (M.op x (M.op y (M.op y (σ x))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13441 X0 X1 X2
       have i₂ := eq1814 (M.op (M.op X0 X2) x) (M.op y sF2) y x
       grind)
    | (have i₁ := eq13441 X0 X1 X2
       have i₂ := eq1814 (M.op (M.op X0 X2) x) y (M.op y sF2) x
       grind)
    | exact superpose eq1814 eq13441
    | exact resolve eq13441 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13441
  have eq13470 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 (σ x))) = (M.op (M.op (M.op X0 X2) x) (M.op x (σ x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13456 X0 X1 X2
       have i₂ := eq1815 x sF2 y
       grind)
    | exact superpose eq1815 eq13456
    | exact resolve eq13456 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13456
  have eq13654 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 y)) = (M.op (M.op (M.op X0 x) X1) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4590 (M.op X0 X1) X2
       have i₂ := eq4524 X0 X1 x
       grind)
    | (have i₁ := eq4590 (M.op X0 X1) X2
       have i₂ := eq4524 X0 x X1
       grind)
    | exact superpose eq4524 eq4590
    | exact resolve eq4590 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13700 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4590 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       have i₂ := eq3487 X0 X1 X2
       grind)
    | exact superpose eq3487 eq4590
    | exact resolve eq4590 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13915 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13700 X0 X1 X2
       have i₂ := eq8039 (M.op X0 X1) (M.op X2 X2) x sF0
       grind)
    | (have i₁ := eq13700 X0 X1 X2
       have i₂ := eq8039 (M.op X0 X1) sF0 (M.op X2 X2) x
       grind)
    | exact superpose eq8039 eq13700
    | exact resolve eq13700 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13700
  have eq14028 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 X1) x) x) y) := by
    intro X0 X1
    first
    | exact superpose eq6696 eq13915
    | exact resolve eq13915 eq6696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696 eq13915
  have eq15424 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op x y) X0) X2)) = (M.op X1 (M.op (M.op y X2) (M.op x X0))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2383 eq525
    | exact resolve eq525 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq15455 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op x y) X0) X2)) = (M.op X1 (M.op y (M.op X2 (M.op x X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15424 X0 X1 X2
       have i₂ := eq1659 y X1 X2 (M.op x X0)
       grind)
    | exact superpose eq1659 eq15424
    | exact resolve eq15424 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15424
  have eq15540 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y (M.op X2 (M.op x X0)))) = (M.op X1 (M.op (M.op x y) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15455 X2 X1 x
       have i₂ := eq1659 sF0 X1 X2 x
       grind)
    | exact superpose eq1659 eq15455
    | exact resolve eq15455 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15455
  have eq15587 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y (M.op X2 (M.op x X0)))) = (M.op X1 (M.op x (M.op y (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1654 eq15540
    | exact resolve eq15540 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15540
  have eq16629 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op y (M.op X0 (M.op x X0))))) := by
    intro X0
    first
    | (have i₁ := eq135 (M.op x X0)
       have i₂ := eq2831 X0 (M.op x X0)
       grind)
    | exact superpose eq2831 eq135
    | exact resolve eq135 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16650 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) (M.op y (M.op X0 X1))) (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3487 (M.op x X0) X1 X2
       have i₂ := eq2831 X0 X1
       grind)
    | exact superpose eq2831 eq3487
    | exact resolve eq3487 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16717 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) (M.op y (M.op X0 X1))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16650 X0 x X2
       have i₂ := eq8039 sF0 (M.op y (M.op X0 x)) (M.op X2 X2) x
       grind)
    | (have i₁ := eq16650 X0 X1 X2
       have i₂ := eq8039 sF0 X1 (M.op y (M.op X0 X1)) (M.op X2 X2)
       grind)
    | exact superpose eq8039 eq16650
    | exact resolve eq16650 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16650
  have eq16735 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x (M.op y (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq16629 X0
       have i₂ := eq15587 X0 sF0 X0
       grind)
    | exact superpose eq15587 eq16629
    | exact resolve eq16629 eq15587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15587 eq16629
  have eq16812 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) (M.op X0 X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16717 X0 X1 x
       have i₂ := eq6691 (M.op sF0 X1) (M.op X0 X1) y x
       grind)
    | exact superpose eq6691 eq16717
    | exact resolve eq16717 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16717
  have eq16830 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16735 X0
       have i₂ := eq1677 y x X0
       grind)
    | exact superpose eq1677 eq16735
    | exact resolve eq16735 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16735
  have eq16886 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16812 X1 x
       have i₂ := eq8134 (M.op sF0 x) X1 x y
       grind)
    | exact superpose eq8134 eq16812
    | exact resolve eq16812 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16812
  have eq16897 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq16830 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16830
    | (have j0 := eq16830 X0
       grind)
    | exact resolve eq16830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16830
  have eq16943 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq16897 X0
       have i₂ := eq135 sF0
       grind)
    | exact superpose eq135 eq16897
    | exact resolve eq16897 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16897
  have eq16969 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq16943
    | (have j0 := eq16943 X0
       grind)
    | exact resolve eq16943 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16943
  have eq17260 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X1 X0) X2))) = (M.op (M.op (σ x) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2926 (M.op X1 X2) X1
       have i₂ := eq1808 sF2 X1 X2
       grind)
    | (have i₁ := eq2926 (M.op X2 X1) X1
       have i₂ := eq1808 sF2 X1 X2
       grind)
    | exact superpose eq1808 eq2926
    | exact resolve eq2926 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17344 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) (M.op X2 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2926 eq1808
    | exact resolve eq1808 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17387 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X2 X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2926 eq17344
    | exact resolve eq17344 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17344
  have eq17469 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X1 X0) X2))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2926 eq17260
    | exact resolve eq17260 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17260
  have eq17555 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X1 X0) X2))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17469 X0 X2 x
       have i₂ := eq1659 X0 sF3 X2 x
       grind)
    | exact superpose eq1659 eq17469
    | exact resolve eq17469 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17469
  have eq17623 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X1 X2)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17555 X2 X0 x
       have i₂ := eq1659 X0 sF3 X2 x
       grind)
    | exact superpose eq1659 eq17555
    | exact resolve eq17555 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17555
  have eq17802 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4624 (M.op X0 sF0) X1
       have i₂ := eq3569 X0 sF0 X2
       grind)
    | (have i₁ := eq4624 (M.op X0 sF0) X1
       have i₂ := eq3569 X0 X1 sF0
       grind)
    | exact superpose eq3569 eq4624
    | exact resolve eq4624 eq3569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17889 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op X0 y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq4624 eq2336
    | exact resolve eq2336 eq4624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17891 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 x) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq4624 eq4524
    | exact resolve eq4524 eq4624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17981 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 x) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1808 (M.op X0 x) X1 y
       have i₂ := eq4624 X0 X1
       grind)
    | exact superpose eq4624 eq1808
    | exact resolve eq1808 eq4624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17986 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 x)) = (M.op X2 (M.op (M.op X1 y) (M.op (M.op X0 (M.op x y)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq525 X2 (M.op X1 y) (M.op X0 x)
       have i₂ := eq4624 X0 X1
       grind)
    | exact superpose eq4624 eq525
    | exact resolve eq525 eq4624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4624
  have eq18018 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 x)) = (M.op X2 (M.op X1 (M.op y (M.op (M.op X0 (M.op x y)) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17986 X0 X0 X1
       have i₂ := eq1659 X0 X1 y (M.op (M.op X0 sF0) X0)
       grind)
    | exact superpose eq1659 eq17986
    | exact resolve eq17986 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17986
  have eq18218 : (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)) y) := by
    first
    | (have i₁ := eq17889 x
       have i₂ := eq2201 (M.op x y) x (M.op sF4 x) (M.op sF3 x)
       grind)
    | (have i₁ := eq17889 x
       have i₂ := eq2201 sF3 x (M.op sF4 x) y
       grind)
    | exact superpose eq2201 eq17889
    | exact resolve eq17889 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17889
  have eq18297 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17802 X0 X1 X2
       have i₂ := eq4524 X0 sF0 x
       grind)
    | (have i₁ := eq17802 X0 X1 X2
       have i₂ := eq4524 X0 x sF0
       grind)
    | exact superpose eq4524 eq17802
    | exact resolve eq17802 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq18314 : ∀ X0 X2 : G, (M.op X2 (M.op X0 x)) = (M.op X2 (M.op y (M.op X0 (M.op x y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq18018 X0 X0 x
       have i₂ := eq2778 X0 x y (M.op X0 sF0)
       grind)
    | exact superpose eq2778 eq18018
    | (have j1 := eq2778 y X2 X0 x
       grind)
    | exact resolve eq18018 eq2778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18018
  have eq18472 : (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) y) (σ y)) := by
    first
    | (have i₁ := eq18218
       have i₂ := eq4524 (M.op sF4 x) sF3 y
       grind)
    | (have i₁ := eq18218
       have i₂ := eq4524 (M.op sF4 x) y sF3
       grind)
    | exact superpose eq4524 eq18218
    | exact resolve eq18218 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18218
  have eq18535 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) x) (M.op y (M.op X2 y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq17981 eq18297
    | exact resolve eq18297 eq17981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18297
  have eq18696 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18535 X0 X1 X2
       have i₂ := eq525 (M.op (M.op X0 x) x) y X2
       grind)
    | exact superpose eq525 eq18535
    | exact resolve eq18535 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18535
  have eq18889 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) x) y)) (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq18472 eq1785
    | exact resolve eq1785 eq18472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785 eq18472
  have eq18929 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op x y)) y)) (M.op (M.op (σ x) (σ y)) x)) := by
    first
    | (have i₁ := eq18889
       have i₂ := eq1812 (M.op sF4 x) sF4 (M.op sF2 sF0) y
       grind)
    | (have i₁ := eq18889
       have i₂ := eq1812 (M.op sF2 sF0) sF4 (M.op sF4 x) y
       grind)
    | exact superpose eq1812 eq18889
    | exact resolve eq18889 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18889
  have eq18951 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) x)) (M.op y (M.op (σ x) (M.op x y)))) := by
    first
    | (have i₁ := eq18929
       have i₂ := eq8134 sF4 (M.op sF2 sF0) y (M.op sF4 x)
       grind)
    | (have i₁ := eq18929
       have i₂ := eq8134 sF4 x sF4 (M.op (M.op sF2 sF0) y)
       grind)
    | exact superpose eq8134 eq18929
    | exact resolve eq18929 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18929
  have eq18973 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op y (M.op (σ x) (M.op x y)))) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq18951
       have i₂ := eq8134 sF4 sF4 x (M.op y (M.op sF2 sF0))
       grind)
    | (have i₁ := eq18951
       have i₂ := eq8134 sF4 (M.op sF2 sF0) y (M.op sF4 x)
       grind)
    | exact superpose eq8134 eq18951
    | exact resolve eq18951 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18951
  have eq18994 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (M.op x y)) y)) := by
    first
    | (have i₁ := eq18973
       have i₂ := eq8134 sF4 y (M.op sF2 sF0) (M.op x sF4)
       grind)
    | (have i₁ := eq18973
       have i₂ := eq8134 sF4 sF4 x (M.op y (M.op sF2 sF0))
       grind)
    | exact superpose eq8134 eq18973
    | exact resolve eq18973 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18973
  have eq19009 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq18994
       have i₂ := eq1659 sF2 (M.op sF4 (M.op x sF4)) sF0 y
       grind)
    | exact superpose eq1659 eq18994
    | exact resolve eq18994 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18994
  have eq19023 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op (σ x) (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq19009
       have i₂ := eq1814 (M.op sF4 (M.op x sF4)) sF0 y sF2
       grind)
    | (have i₁ := eq19009
       have i₂ := eq1814 (M.op sF4 (M.op x sF4)) y sF0 sF2
       grind)
    | exact superpose eq1814 eq19009
    | exact resolve eq19009 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19009
  have eq19033 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op y (M.op (σ x) (M.op x y)))) := by
    first
    | (have i₁ := eq19023
       have i₂ := eq3372 sF2 sF0 (M.op sF4 (M.op x sF4)) y
       grind)
    | (have i₁ := eq19023
       have i₂ := eq3372 y sF0 (M.op sF4 (M.op x sF4)) sF2
       grind)
    | exact superpose eq3372 eq19023
    | exact resolve eq19023 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19023
  have eq19041 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ x) (σ y)))) (M.op (σ x) x)) := by
    first
    | exact superpose eq18314 eq19033
    | exact resolve eq19033 eq18314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18314 eq19033
  have eq19047 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19041
       have i₂ := eq2201 (M.op x sF4) x sF4 (M.op sF2 x)
       grind)
    | (have i₁ := eq19041
       have i₂ := eq2201 sF2 x sF4 sF4
       grind)
    | exact superpose eq2201 eq19041
    | exact resolve eq19041 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201 eq19041
  have eq19444 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq4643 eq1808
    | exact resolve eq1808 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643
  have eq21089 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ y)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq2566 eq3465
    | exact resolve eq3465 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21620 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ x) (M.op X0 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3390 x X1
       have i₂ := eq1808 sF2 sF3 x
       grind)
    | (have i₁ := eq3390 X1 X1
       have i₂ := eq1808 sF2 X1 sF3
       grind)
    | exact superpose eq1808 eq3390
    | exact resolve eq3390 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21750 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) = (M.op X2 (M.op (M.op (σ x) (M.op (σ y) X1)) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3390 eq1808
    | exact resolve eq1808 eq3390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21803 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) = (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq3390 eq2926
    | exact resolve eq2926 eq3390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21826 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) X1))) := by
    intro X0 X1
    first
    | exact superpose eq2926 eq21803
    | exact resolve eq21803 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21803
  have eq21868 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) = (M.op X2 (M.op (σ x) (M.op (M.op (σ y) X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21750 x X1 X1
       have i₂ := eq1659 sF2 X1 (M.op sF3 X1) x
       grind)
    | exact superpose eq1659 eq21750
    | exact resolve eq21750 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21750
  have eq22010 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq21826 X0 x
       have i₂ := eq1659 X0 sF3 sF4 x
       grind)
    | exact superpose eq1659 eq21826
    | exact resolve eq21826 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21826
  have eq22035 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (M.op (σ y) (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21868 x X2 X2
       have i₂ := eq1659 sF3 sF2 X2 x
       grind)
    | exact superpose eq1659 eq21868
    | exact resolve eq21868 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21868
  have eq22132 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (M.op (M.op (σ y) X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22010 X0 x
       have i₂ := eq1659 sF2 sF3 (M.op sF3 X0) x
       grind)
    | exact superpose eq1659 eq22010
    | exact resolve eq22010 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22010
  have eq22222 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22132 X0 X1
       have i₂ := eq3372 sF3 (M.op (M.op sF3 X0) X1) sF4 sF2
       grind)
    | (have i₁ := eq22132 X0 X1
       have i₂ := eq3372 sF2 (M.op (M.op sF3 X0) X1) sF4 sF3
       grind)
    | exact superpose eq3372 eq22132
    | exact resolve eq22132 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22132
  have eq22270 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq22222 x x
       have i₂ := eq1659 sF3 sF3 x x
       grind)
    | exact superpose eq1659 eq22222
    | exact resolve eq22222 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22222
  have eq22293 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22270 X0 X1
       have i₂ := eq1815 sF2 (M.op X0 X1) sF3
       grind)
    | exact superpose eq1815 eq22270
    | exact resolve eq22270 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22270
  have eq22305 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (σ y) X1))))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq1655 eq22293
    | exact resolve eq22293 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22293
  have eq22528 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op x y)))) = (M.op X2 (M.op (M.op x (M.op y X1)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1808 X2 X0 (M.op x (M.op y X1))
       have i₂ := eq3391 X1 X0
       grind)
    | exact superpose eq3391 eq1808
    | exact resolve eq1808 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22647 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op x y)))) = (M.op X2 (M.op x (M.op (M.op y X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22528 X0 X1 X2
       have i₂ := eq1659 x X2 (M.op y X1) X0
       grind)
    | exact superpose eq1659 eq22528
    | exact resolve eq22528 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22528
  have eq22831 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x (M.op y (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22647 X0 X1 X2
       have i₂ := eq1659 y x X1 X0
       grind)
    | exact superpose eq1659 eq22647
    | exact resolve eq22647 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22647
  have eq23267 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op X0 X1) (M.op X2 X2))) = (M.op (M.op (M.op (M.op x y) y) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4044 X1 (M.op (M.op X0 X1) (M.op X2 X2))
       have i₂ := eq3487 X0 X1 X2
       grind)
    | exact superpose eq3487 eq4044
    | exact resolve eq4044 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4044
  have eq23438 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) y) X1) X0) = (M.op x (M.op X0 (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23267 X0 X1 X2
       have i₂ := eq1659 X0 x X1 (M.op X2 X2)
       grind)
    | exact superpose eq1659 eq23267
    | exact resolve eq23267 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23267
  have eq23547 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op (M.op x y) y) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23438 X0 X1 x
       have i₂ := eq1677 X1 X0 x
       grind)
    | exact superpose eq1677 eq23438
    | exact resolve eq23438 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23438
  have eq23790 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) x) y) = (M.op X0 (M.op (M.op X2 X1) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4452 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq1710 X0 X1 X2
       grind)
    | exact superpose eq1710 eq4452
    | exact resolve eq4452 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24060 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op x y)))) = (M.op (M.op (M.op (M.op X0 X1) X2) x) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23790 X1 X2 X0
       have i₂ := eq1659 X0 X1 X2 sF0
       grind)
    | exact superpose eq1659 eq23790
    | exact resolve eq23790 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23790
  have eq24210 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14028 X0 X1
       have i₂ := eq24060 X0 X1 x
       grind)
    | exact superpose eq24060 eq14028
    | exact resolve eq14028 eq24060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14028 eq24060
  have eq24575 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) X0) (M.op (M.op (σ y) X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2336 eq4455
    | exact resolve eq4455 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24585 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (σ x)) (σ y)) = (M.op X0 (M.op (M.op X2 X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4455 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq1710 X0 X1 X2
       grind)
    | exact superpose eq1710 eq4455
    | exact resolve eq4455 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24827 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op (σ x) (σ y))))) = (M.op (M.op (M.op (M.op X0 X1) X2) (σ x)) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24585 X1 X2 X0
       have i₂ := eq1659 X0 X1 X2 sF4
       grind)
    | exact superpose eq1659 eq24585
    | exact resolve eq24585 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24585
  have eq24835 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ y) X1) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq2926 eq24575
    | exact resolve eq24575 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24575
  have eq24972 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X1))))) := by
    intro X0 X1
    first
    | exact superpose eq17387 eq24835
    | exact resolve eq24835 eq17387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17387 eq24835
  have eq25062 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ y) X1)))))) := by
    intro X0 X1
    first
    | exact superpose eq1655 eq24972
    | exact resolve eq24972 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24972
  have eq25127 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq22305 eq25062
    | exact resolve eq25062 eq22305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22305 eq25062
  have eq25165 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq24827 eq25127
    | exact resolve eq25127 eq24827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24827 eq25127
  have eq26979 : ∀ X0 X1 : G, (M.op x (M.op X1 y)) = (M.op (M.op (M.op (M.op x y) X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7494 X1 x
       have i₂ := eq4524 sF0 X1 x
       grind)
    | (have i₁ := eq7494 x X1
       have i₂ := eq4524 sF0 X1 x
       grind)
    | exact superpose eq4524 eq7494
    | exact resolve eq7494 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7494
  have eq27991 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ y) X2) (M.op (σ x) X0))) = (M.op X1 (M.op (M.op (M.op (σ x) (σ y)) X2) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq8031 eq525
    | exact resolve eq525 eq8031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8031
  have eq28032 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ y) X2) (M.op (σ x) X0))) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27991 x X1 X2
       have i₂ := eq1659 sF4 X1 X2 x
       grind)
    | exact superpose eq1659 eq27991
    | exact resolve eq27991 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27991
  have eq28138 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (σ y) X2) (M.op (σ x) X0))) = (M.op X1 (M.op (σ x) (M.op (σ y) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1655 eq28032
    | exact resolve eq28032 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28032
  have eq28199 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ y) (M.op X2 (M.op (σ x) X0)))) = (M.op X1 (M.op (σ x) (M.op (σ y) (M.op X2 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28138 X0 X1 X2
       have i₂ := eq1659 sF3 X1 X2 (M.op sF2 X0)
       grind)
    | exact superpose eq1659 eq28138
    | exact resolve eq28138 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28138
  have eq29229 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) (M.op X0 (σ y))) y) X1) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq7493 eq8047
    | exact resolve eq8047 eq7493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7493
  have eq29383 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) y) (M.op (σ y) X0)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq29229 X1 X1
       have i₂ := eq8134 sF2 X1 sF3 y
       grind)
    | exact superpose eq8134 eq29229
    | exact resolve eq29229 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29229
  have eq29424 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) y) (M.op x y)) (M.op (σ y) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29383 X0 x
       have i₂ := eq8039 (M.op sF2 y) (M.op sF3 X0) x sF0
       grind)
    | (have i₁ := eq29383 X0 x
       have i₂ := eq8039 (M.op sF2 y) sF0 (M.op sF3 X0) x
       grind)
    | exact superpose eq8039 eq29383
    | exact resolve eq29383 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29383
  have eq29452 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) y) x) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq17981 eq29424
    | exact resolve eq29424 eq17981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29424
  have eq29472 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) x) y) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29452 X0 X1
       have i₂ := eq4524 sF2 y x
       grind)
    | (have i₁ := eq29452 X0 X1
       have i₂ := eq4524 sF2 x y
       grind)
    | exact superpose eq4524 eq29452
    | exact resolve eq29452 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29452
  have eq29485 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq2926 eq29472
    | exact resolve eq29472 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29472
  have eq29492 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op y (σ y)))) (M.op y (M.op (σ y) X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq2947 eq29485
    | exact resolve eq29485 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29485
  have eq31162 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) (M.op (σ y) X1)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2336 eq13260
    | exact resolve eq13260 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq31175 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op X2 X1)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13260 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq1710 X0 X1 X2
       grind)
    | exact superpose eq1710 eq13260
    | exact resolve eq13260 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13260
  have eq31384 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31175 X0 X2 X1
       have i₂ := eq8134 (M.op X0 sF2) X1 X2 sF4
       grind)
    | exact superpose eq8134 eq31175
    | exact resolve eq31175 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31175
  have eq31397 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) (M.op (σ x) (σ y))) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq31162 X0 x
       have i₂ := eq8134 (M.op (M.op sF2 X0) sF2) sF3 x sF4
       grind)
    | exact superpose eq8134 eq31162
    | exact resolve eq31162 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31162
  have eq31519 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (σ y) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq19444 eq31384
    | exact resolve eq31384 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31384
  have eq31533 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) (σ x)) (M.op (σ y) (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq19444 eq31397
    | exact resolve eq31397 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31397
  have eq31640 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (σ y)) = (M.op (M.op (M.op X0 x) x) (M.op (σ y) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31519 X0 X1 X2
       have i₂ := eq18696 X0 sF2 (M.op sF3 (M.op X1 X2))
       grind)
    | exact superpose eq18696 eq31519
    | exact resolve eq31519 eq18696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31519
  have eq31652 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) x) x) (M.op (σ y) (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31533 X0 X1
       have i₂ := eq18696 (M.op sF2 X0) sF2 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq18696 eq31533
    | exact resolve eq31533 eq18696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31533
  have eq31754 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) X0) x) x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31652 X0 x
       have i₂ := eq525 (M.op (M.op (M.op sF2 X0) x) x) sF3 x
       grind)
    | exact superpose eq525 eq31652
    | exact resolve eq31652 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31652
  have eq31843 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 x))) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq2926 eq31754
    | exact resolve eq31754 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31754
  have eq31914 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op y (σ y)))) (M.op y (M.op (σ y) (M.op (σ y) (M.op X0 x))))) X1) := by
    intro X0 X1
    first
    | exact superpose eq29492 eq31843
    | exact resolve eq31843 eq29492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29492 eq31843
  have eq31961 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op y (σ y)))) (M.op y (M.op X0 x))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31914 X0 X1
       have i₂ := eq1815 y (M.op X0 x) sF3
       grind)
    | exact superpose eq1815 eq31914
    | exact resolve eq31914 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31914
  have eq32001 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op x (M.op y (σ y)))) (M.op x (M.op y X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31961 x X1
       have i₂ := eq3375 y (M.op sF4 (M.op x (M.op y sF3))) x x
       grind)
    | (have i₁ := eq31961 x X1
       have i₂ := eq3375 x (M.op sF4 (M.op x (M.op y sF3))) y x
       grind)
    | exact superpose eq3375 eq31961
    | exact resolve eq31961 eq3375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3375 eq31961
  have eq35439 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op (M.op x y) X0) y) X1) := by
    intro X0 X1
    first
    | exact superpose eq16886 eq1815
    | exact resolve eq1815 eq16886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16886
  have eq36146 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16969 x
       have i₂ := eq135 x
       grind)
    | exact superpose eq135 eq16969
    | exact resolve eq16969 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16969
  have eq36197 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq36146
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36146
    | exact resolve eq36146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36146
  have eq36208 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq2926 eq36197
    | exact resolve eq36197 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36197
  have eq36217 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq28199 eq36208
    | exact resolve eq36208 eq28199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28199 eq36208
  have eq36223 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x))))) := by
    first
    | exact superpose eq10070 eq36217
    | exact resolve eq36217 eq10070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36217
  have eq36228 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq25165 eq36223
    | exact resolve eq36223 eq25165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25165 eq36223
  have eq36233 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq36228
       have i₂ := eq1815 sF4 sF4 sF2
       grind)
    | exact superpose eq1815 eq36228
    | exact resolve eq36228 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36228
  have eq36288 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq36233 eq8032
    | exact resolve eq8032 eq36233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8032
  have eq36294 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq36233 eq236
    | exact resolve eq236 eq36233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36316 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq36233 eq3569
    | exact resolve eq3569 eq36233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36321 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq36233 eq4524
    | exact resolve eq4524 eq36233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36233
  have eq36334 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq36321 eq19047
    | exact resolve eq19047 eq36321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19047
  have eq36360 : (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq36294
       have i₂ := eq236 sF1
       grind)
    | exact superpose eq236 eq36294
    | exact resolve eq36294 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36294
  have eq36365 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op (σ x) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1655 eq36288
    | exact resolve eq36288 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36288
  have eq36394 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq37 eq36360
    | exact resolve eq36360 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq36360
  have eq36396 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq36365 X0
       have i₂ := eq1677 sF2 (M.op (M.op sF1 sF1) X0) sF3
       grind)
    | exact superpose eq1677 eq36365
    | exact resolve eq36365 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36365
  have eq36420 : (k (M.op (M.op x y) (M.op x y)) x) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq36394 eq4917
    | exact resolve eq4917 eq36394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4917
  have eq36452 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq2135 eq36420
    | exact resolve eq36420 eq2135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135 eq36420
  have eq36983 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq36334 eq409
    | exact resolve eq409 eq36334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37101 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (M.op (σ (M.op x y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq36983 eq409
    | exact resolve eq409 eq36983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37105 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op X0 (M.op (σ (M.op x y)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq36983 eq1710
    | exact resolve eq1710 eq36983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37116 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (σ x)) (M.op x y))) := by
    first
    | exact superpose eq36983 eq4452
    | exact resolve eq4452 eq36983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36983
  have eq37133 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op x y)))) := by
    first
    | (have i₁ := eq37116
       have i₂ := eq1659 sF1 sF1 sF2 sF0
       grind)
    | exact superpose eq1659 eq37116
    | exact resolve eq37116 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37116
  have eq37146 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq37101 x
       have i₂ := eq1659 sF1 (M.op sF1 x) sF2 x
       grind)
    | exact superpose eq1659 eq37101
    | exact resolve eq37101 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37101
  have eq37155 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (M.op x y) (σ x)))) := by
    first
    | (have i₁ := eq37133
       have i₂ := eq1814 sF1 sF2 sF0 sF1
       grind)
    | (have i₁ := eq37133
       have i₂ := eq1814 sF1 sF0 sF2 sF1
       grind)
    | exact superpose eq1814 eq37133
    | exact resolve eq37133 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37133
  have eq37171 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op (M.op x y) (M.op (σ (M.op x y)) (σ x)))) := by
    first
    | (have i₁ := eq37155
       have i₂ := eq3372 sF1 sF2 sF1 sF0
       grind)
    | (have i₁ := eq37155
       have i₂ := eq3372 sF0 sF2 sF1 sF1
       grind)
    | exact superpose eq3372 eq37155
    | exact resolve eq37155 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37155
  have eq37183 : (M.op (M.op (σ x) x) y) = (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) := by
    first
    | exact superpose eq1654 eq37171
    | exact resolve eq37171 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37171
  have eq37189 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op x y))) = (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) := by
    first
    | exact superpose eq2926 eq37183
    | exact resolve eq37183 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37183
  have eq37211 : (M.op (M.op (σ x) (σ y)) (M.op x (M.op y (σ y)))) = (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) := by
    first
    | exact superpose eq2947 eq37189
    | exact resolve eq37189 eq2947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947 eq37189
  have eq37237 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op x (M.op y X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq37211 eq32001
    | exact resolve eq32001 eq37211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32001 eq37211
  have eq37486 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X0)) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq36394 eq3487
    | exact resolve eq3487 eq36394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3487 eq36394
  have eq37512 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) x) (M.op y (M.op X0 X0))) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq17981 eq37486
    | exact resolve eq37486 eq17981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37486
  have eq37532 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) x) y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq37512 x
       have i₂ := eq1677 y (M.op sF0 x) x
       grind)
    | exact superpose eq1677 eq37512
    | exact resolve eq37512 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37512
  have eq37543 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq35439 eq37532
    | exact resolve eq37532 eq35439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35439 eq37532
  have eq38661 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq36316 eq4455
    | exact resolve eq4455 eq36316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36316
  have eq38754 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq19444 eq38661
    | exact resolve eq38661 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38661
  have eq38858 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) (M.op (σ x) (M.op (σ y) (M.op X0 (σ y))))) := by
    intro X0
    first
    | exact superpose eq22035 eq38754
    | exact resolve eq38754 eq22035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22035 eq38754
  have eq38935 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq38858 x
       have i₂ := eq525 sF2 sF3 x
       grind)
    | exact superpose eq525 eq38858
    | exact resolve eq38858 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38858
  have eq38986 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq36334 eq38935
    | exact resolve eq38935 eq36334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36334 eq38935
  have eq39028 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op x (M.op y X0))) (σ x)) := by
    intro X0
    first
    | exact superpose eq37237 eq38986
    | exact resolve eq38986 eq37237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37237 eq38986
  have eq39064 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (M.op x (M.op y (M.op (σ (M.op x y)) (σ x))))) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq39028 X0
       have i₂ := eq8039 sF1 (M.op x (M.op y (M.op sF1 sF2))) (M.op x (M.op y X0)) sF2
       grind)
    | (have i₁ := eq39028 X0
       have i₂ := eq8039 sF1 sF2 (M.op x (M.op y (M.op sF1 sF2))) (M.op x (M.op y X0))
       grind)
    | exact superpose eq8039 eq39028
    | exact resolve eq39028 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39028
  have eq39309 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) X1) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq36321 eq1710
    | exact resolve eq1710 eq36321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36321
  have eq39350 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq39309 x x
       have i₂ := eq4607 sF1 sF1 x sF4 x
       grind)
    | exact superpose eq4607 eq39309
    | exact resolve eq39309 eq4607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4607 eq39309
  have eq39406 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) X0)))) := by
    intro X0
    first
    | exact superpose eq1655 eq39350
    | exact resolve eq39350 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq39350
  have eq39434 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq10070 eq39406
    | exact resolve eq39406 eq10070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39406
  have eq39565 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | exact superpose eq39434 eq2926
    | exact resolve eq2926 eq39434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq39569 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X1 (M.op X0 X2)))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op X0 (M.op X1 X2))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq39434 eq17623
    | exact resolve eq17623 eq39434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17623
  have eq39633 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X1 (M.op X0 X2)))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39569 X0 X1 X2
       have i₂ := eq1815 sF2 (M.op X0 (M.op X1 X2)) sF3
       grind)
    | exact superpose eq1815 eq39569
    | exact resolve eq39569 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39569
  have eq39637 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq39565 X0 X1
       have i₂ := eq1815 sF2 (M.op X0 X1) sF3
       grind)
    | exact superpose eq1815 eq39565
    | exact resolve eq39565 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39565
  have eq39749 : ∀ X0 X1 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 (M.op X1 X2))))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op X1 (M.op X0 X2))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq39434 eq39633
    | exact resolve eq39633 eq39434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39633
  have eq39830 : ∀ X0 X1 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 (M.op X1 X2))))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39749 X0 X1 X2
       have i₂ := eq1815 sF2 (M.op X1 (M.op X0 X2)) sF3
       grind)
    | exact superpose eq1815 eq39749
    | exact resolve eq39749 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39749
  have eq40695 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq36396 x
       have i₂ := eq4524 sF1 sF1 x
       grind)
    | (have i₁ := eq36396 x
       have i₂ := eq4524 sF1 x sF1
       grind)
    | exact superpose eq4524 eq36396
    | exact resolve eq36396 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36396
  have eq41150 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ (M.op x y)) (σ x)))) = (M.op (M.op (M.op (σ (M.op x y)) X0) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq37105 eq3569
    | exact resolve eq3569 eq37105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37105
  have eq45152 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op X3 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4455 eq398
    | exact resolve eq398 eq4455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455
  have eq45175 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) (M.op X2 (σ x))) = (M.op (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq40695 eq398
    | exact resolve eq398 eq40695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40695
  have eq45210 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X2) X1)) = (M.op (M.op X0 (M.op X2 y)) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq2055 eq398
    | exact resolve eq398 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45667 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op y X2)) = (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45210 X0 X1 X2
       have i₂ := eq8134 X0 X2 y x
       grind)
    | exact superpose eq8134 eq45210
    | exact resolve eq45210 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45210
  have eq45689 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X1) (M.op X2 X1)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 (M.op X2 (σ x)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq39637 eq45175
    | exact resolve eq45175 eq39637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45175
  have eq45708 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op X4 (M.op (M.op X3 (M.op X4 X2)) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1845 X0 X1 X2 X3 X4 x
       have i₂ := eq45152 X0 (M.op X3 (M.op X4 X2)) x X4
       grind)
    | exact superpose eq45152 eq1845
    | exact resolve eq1845 eq45152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845 eq45152
  have eq45968 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op y X2)) = (M.op (M.op X0 X1) (M.op (M.op x y) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45667 X0 x X2
       have i₂ := eq1659 sF0 (M.op X0 x) X2 x
       grind)
    | exact superpose eq1659 eq45667
    | exact resolve eq45667 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45667
  have eq45980 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X1) (M.op X2 X1)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45689 X2 X1 x
       have i₂ := eq2778 sF2 sF1 X2 x
       grind)
    | exact superpose eq2778 eq45689
    | exact resolve eq45689 eq2778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778 eq45689
  have eq45994 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op X4 (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op X4 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq45708 X0 X1 X2 X3 X4
       have i₂ := eq1814 (M.op (M.op X0 sF2) sF3) (M.op X3 (M.op X4 X2)) sF4 X4
       grind)
    | (have i₁ := eq45708 X0 X1 X2 X3 X4
       have i₂ := eq1814 (M.op (M.op X0 sF2) sF3) sF4 (M.op X3 (M.op X4 X2)) X4
       grind)
    | exact superpose eq1814 eq45708
    | exact resolve eq45708 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45708
  have eq46171 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x (M.op y (M.op X2 X1)))) = (M.op (M.op X0 x) (M.op y X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1654 eq45968
    | exact resolve eq45968 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45968
  have eq46188 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op X4 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X3 (M.op X4 X2)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq39434 eq45994
    | exact resolve eq45994 eq39434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45994
  have eq46297 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) x) (M.op y (σ (M.op x y)))) (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq39064 X0
       have i₂ := eq46171 sF1 sF2 sF1
       grind)
    | exact superpose eq46171 eq39064
    | exact resolve eq39064 eq46171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39064 eq46171
  have eq46306 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op X4 (M.op (σ x) (M.op (σ y) (M.op X3 (M.op X4 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq46188 X0 X1 X2 X3 X0
       have i₂ := eq1815 X0 (M.op sF2 (M.op sF3 (M.op X3 (M.op X0 X2)))) sF1
       grind)
    | exact superpose eq1815 eq46188
    | exact resolve eq46188 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46188
  have eq46586 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op x X0)) = (M.op (M.op X2 (M.op (M.op x y) (M.op y (M.op X0 X1)))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1812 X3 X2 (M.op x X0) X1
       have i₂ := eq2831 X0 X1
       grind)
    | exact superpose eq2831 eq1812
    | exact resolve eq1812 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46614 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 (M.op x y))) (M.op (M.op (M.op X0 x) y) X1)) = (M.op (M.op X2 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq8047 eq1812
    | exact resolve eq1812 eq8047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8047
  have eq46658 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op x y))) X2) = (M.op (M.op X0 (M.op X2 (M.op y X1))) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1812 X2 X0 x (M.op y X1)
       have i₂ := eq3391 X1 X0
       grind)
    | exact superpose eq3391 eq1812
    | exact resolve eq1812 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391
  have eq46680 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq2566 eq1812
    | exact resolve eq1812 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566
  have eq46912 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1)) X2) = (M.op (M.op X0 (M.op X2 X1)) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2165 (M.op X1 (M.op X0 x))
       have i₂ := eq1812 X0 X1 (M.op sF2 sF4) x
       grind)
    | (have i₁ := eq2165 (M.op X1 (M.op X2 x))
       have i₂ := eq1812 (M.op sF2 sF4) X1 X2 x
       grind)
    | exact superpose eq1812 eq2165
    | exact resolve eq2165 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46929 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 (M.op (σ x) X1)) X2) (σ y)) X3) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8051 (M.op X1 (M.op X0 x)) X1
       have i₂ := eq1812 X0 X1 sF2 x
       grind)
    | (have i₁ := eq8051 (M.op X1 (M.op X2 x)) X1
       have i₂ := eq1812 sF2 X1 X2 x
       grind)
    | exact superpose eq1812 eq8051
    | exact resolve eq8051 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8051
  have eq46942 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) X2) X3) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq46929 X0 X1 X2 X3
       have i₂ := eq8039 X0 (M.op sF2 X1) X2 sF3
       grind)
    | (have i₁ := eq46929 X0 X1 X3 X3
       have i₂ := eq8039 X0 sF3 (M.op sF2 X1) X3
       grind)
    | exact superpose eq8039 eq46929
    | exact resolve eq46929 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46929
  have eq46959 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1)) X2) = (M.op (M.op X0 (σ y)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46912 X0 X2 X1
       have i₂ := eq8134 X0 X1 X2 sF3
       grind)
    | exact superpose eq8134 eq46912
    | exact resolve eq46912 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46912
  have eq47255 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (σ y) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq19444 eq46680
    | exact resolve eq46680 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46680
  have eq47275 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op x y))) X2) = (M.op (M.op X0 x) (M.op (M.op y X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46658 X0 X1 X2
       have i₂ := eq8134 X0 X2 (M.op y X1) x
       grind)
    | exact superpose eq8134 eq46658
    | exact resolve eq46658 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46658
  have eq47314 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X1)) X3) = (M.op (M.op X2 (M.op X3 (M.op x y))) (M.op (M.op X0 x) (M.op y X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq46614 X0 X3 X2 X3
       have i₂ := eq1659 (M.op X0 x) (M.op X2 (M.op X3 sF0)) y X3
       grind)
    | exact superpose eq1659 eq46614
    | exact resolve eq46614 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46614
  have eq47342 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op x X0)) = (M.op (M.op X2 (M.op x (M.op y (M.op y (M.op X0 X1))))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1654 eq46586
    | exact resolve eq46586 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46586
  have eq47518 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46959 X1 x X2
       have i₂ := eq1659 sF2 X1 sF4 x
       grind)
    | exact superpose eq1659 eq46959
    | exact resolve eq46959 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46959
  have eq47767 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (σ y)) = (M.op (M.op (M.op X0 x) x) (M.op (σ y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47255 X0 X1 X2
       have i₂ := eq18696 X0 sF2 (M.op sF3 X2)
       grind)
    | exact superpose eq18696 eq47255
    | exact resolve eq47255 eq18696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47255
  have eq47780 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op x y))) X2) = (M.op (M.op X0 x) (M.op y (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47275 X0 X1 X2
       have i₂ := eq1659 y (M.op X0 x) X1 X2
       grind)
    | exact superpose eq1659 eq47275
    | exact resolve eq47275 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47275
  have eq47807 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X1)) X3) = (M.op (M.op X2 (M.op X3 (M.op x y))) (M.op X0 (M.op x (M.op y X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47314 X0 X1 X2 X3
       have i₂ := eq1659 X0 (M.op X2 (M.op X3 sF0)) x (M.op y X1)
       grind)
    | exact superpose eq1659 eq47314
    | exact resolve eq47314 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47314
  have eq47830 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op x X0)) = (M.op (M.op X2 (M.op x (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47342 X0 X1 X2 X3
       have i₂ := eq1815 x (M.op X0 X1) y
       grind)
    | exact superpose eq1815 eq47342
    | exact resolve eq47342 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47342
  have eq47943 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X1)))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq39434 eq47518
    | exact resolve eq47518 eq39434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47518
  have eq48118 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) x) (M.op (σ y) X2)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47767 X0 X2 X1
       have i₂ := eq8134 (M.op X0 X2) X1 X2 sF3
       grind)
    | exact superpose eq8134 eq47767
    | exact resolve eq47767 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47767
  have eq48269 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X1)) X3) = (M.op (M.op X2 x) (M.op y (M.op X3 (M.op X0 (M.op x (M.op y X1)))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq47780 eq47807
    | exact resolve eq47807 eq47780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47780 eq47807
  have eq48331 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X1)))))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47943 x X1 X2
       have i₂ := eq3372 sF2 (M.op sF1 (M.op sF2 (M.op sF3 X1))) x sF1
       grind)
    | (have i₁ := eq47943 x X1 X2
       have i₂ := eq3372 sF1 (M.op sF1 (M.op sF2 (M.op sF3 X1))) x sF2
       grind)
    | exact superpose eq3372 eq47943
    | exact resolve eq47943 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47943
  have eq48605 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (σ y) X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48331 x X1 X2
       have i₂ := eq8170 sF2 sF1 (M.op sF2 (M.op sF3 X1)) x
       grind)
    | exact superpose eq8170 eq48331
    | exact resolve eq48331 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48331
  have eq48793 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) X1)) X2) = (M.op (M.op X0 (σ y)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48605 X0 X1 X2
       have i₂ := eq1815 X0 (M.op sF3 X1) sF2
       grind)
    | exact superpose eq1815 eq48605
    | exact resolve eq48605 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48605
  have eq50707 : ∀ X0 : G, (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36452
       have i₂ := eq3465 X0 sF2 sF2
       grind)
    | (have i₁ := eq36452
       have i₂ := eq3465 sF2 sF2 x
       grind)
    | exact superpose eq3465 eq36452
    | exact resolve eq36452 eq3465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50708 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x x))) := by
    first
    | exact superpose eq36452 eq11
    | exact resolve eq11 eq36452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36452
  have eq50878 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq50708
       have i₂ := eq3465 X0 x x
       grind)
    | (have i₁ := eq50708
       have i₂ := eq3465 x x X0
       grind)
    | exact superpose eq3465 eq50708
    | exact resolve eq50708 eq3465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3465 eq50708
  have eq51244 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) (M.op X1 y)) (M.op X3 (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq17891 eq398
    | exact resolve eq398 eq17891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq51284 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 x) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1808 (M.op X0 x) X1 y
       have i₂ := eq17891 X0 X1
       grind)
    | (have i₁ := eq1808 (M.op X0 X1) x y
       have i₂ := eq17891 X0 X1
       grind)
    | exact superpose eq17891 eq1808
    | exact resolve eq1808 eq17891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17891
  have eq52221 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op y X1)) X2) = (M.op (M.op (M.op X0 x) x) (M.op y X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1233 eq17981
    | exact resolve eq17981 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op X0 (M.op X2 (M.op X1 (M.op x y)))) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq24210 eq1812
    | exact resolve eq1812 eq24210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24210
  have eq56885 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op x y)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56685 X0 X1 X1
       have i₂ := eq8134 X0 X1 (M.op X1 sF0) x
       grind)
    | exact superpose eq8134 eq56685
    | exact resolve eq56685 eq8134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8134 eq56685
  have eq57012 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op X0 x) (M.op X1 (M.op (M.op x y) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56885 X0 X0 x
       have i₂ := eq1659 X0 (M.op X0 x) sF0 x
       grind)
    | exact superpose eq1659 eq56885
    | exact resolve eq56885 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56885
  have eq57125 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 y)) X2) = (M.op (M.op X0 x) (M.op X1 (M.op x (M.op y X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1654 eq57012
    | exact resolve eq57012 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57012
  have eq57236 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op x (M.op y (M.op X3 (M.op x y)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51244 X0 X1 X2 X3
       have i₂ := eq57125 (M.op X0 x) X1 (M.op X3 sF0)
       grind)
    | exact superpose eq57125 eq51244
    | exact resolve eq51244 eq57125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51244 eq57125
  have eq57311 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op x (M.op x (M.op y (M.op X3 y)))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq22831 eq57236
    | exact resolve eq57236 eq22831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22831 eq57236
  have eq57368 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op y (M.op X3 y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57311 X0 X1 X2 X3
       have i₂ := eq1815 X1 (M.op y (M.op X3 y)) x
       grind)
    | exact superpose eq1815 eq57311
    | exact resolve eq57311 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57311
  have eq57418 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57368 X0 X1 X2 X3
       have i₂ := eq525 X1 y X3
       grind)
    | exact superpose eq525 eq57368
    | exact resolve eq57368 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57368
  have eq57458 : ∀ X0 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X2))) = (M.op (M.op (M.op (M.op (σ (M.op x y)) X0) x) x) (M.op (σ (M.op x y)) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq45980 X0 X2 x
       have i₂ := eq57418 (M.op sF1 X0) sF1 X2 x
       grind)
    | exact superpose eq57418 eq45980
    | exact resolve eq45980 eq57418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45980
  have eq57499 : ∀ X0 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X2))) = (M.op (M.op (σ x) (M.op X0 (M.op (σ (M.op x y)) (σ x)))) (M.op (σ (M.op x y)) X2)) := by
    intro X0 X2
    first
    | exact superpose eq41150 eq57458
    | exact resolve eq57458 eq41150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41150 eq57458
  have eq57534 : ∀ X0 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X2))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (M.op X0 (M.op (σ (M.op x y)) (σ x))) (M.op (σ (M.op x y)) X2))))) := by
    intro X0 X2
    first
    | exact superpose eq39637 eq57499
    | exact resolve eq57499 eq39637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57499
  have eq57558 : ∀ X0 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X2))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ (M.op x y)) (M.op (M.op X0 (M.op (σ (M.op x y)) (σ x))) X2))))) := by
    intro X0 X2
    first
    | exact superpose eq39830 eq57534
    | exact resolve eq57534 eq39830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39830 eq57534
  have eq57589 : ∀ X0 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X2))) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (M.op X0 (M.op (σ (M.op x y)) (σ x))) X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq57558 X0 X2
       have i₂ := eq8170 sF2 sF1 (M.op (M.op X0 (M.op sF1 sF2)) X2) sF1
       grind)
    | exact superpose eq8170 eq57558
    | exact resolve eq57558 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57558
  have eq57612 : ∀ X0 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X2))) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 (M.op (M.op (σ (M.op x y)) (σ x)) X2)))) := by
    intro X0 X2
    first
    | (have i₁ := eq57589 X0 x
       have i₂ := eq1659 X0 sF2 (M.op sF1 sF2) x
       grind)
    | exact superpose eq1659 eq57589
    | exact resolve eq57589 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57589
  have eq57628 : ∀ X0 X2 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 X2))) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 (M.op (σ (M.op x y)) (M.op (σ x) X2))))) := by
    intro X0 X2
    first
    | (have i₁ := eq57612 x x
       have i₂ := eq1659 sF1 x sF2 x
       grind)
    | exact superpose eq1659 eq57612
    | exact resolve eq57612 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57612
  have eq57983 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1814 X3 X1 (M.op X0 X2) X4
       have i₂ := eq4524 X0 X2 X1
       grind)
    | (have i₁ := eq1814 X3 X1 (M.op X0 X2) X4
       have i₂ := eq4524 X0 X1 X2
       grind)
    | exact superpose eq4524 eq1814
    | exact resolve eq1814 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58324 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op X0 (M.op X2 (M.op X4 X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4524 X0 X1 (M.op X2 (M.op X4 X3))
       have i₂ := eq1814 (M.op X0 X1) X4 X3 X2
       grind)
    | (have i₁ := eq4524 X0 X1 (M.op X2 (M.op X4 X3))
       have i₂ := eq1814 (M.op X0 X1) X3 X4 X2
       grind)
    | exact superpose eq1814 eq4524
    | exact resolve eq4524 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58626 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) = (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57983 X1 X0 X2 X3 X4
       have i₂ := eq1659 X1 X4 X0 X2
       grind)
    | exact superpose eq1659 eq57983
    | exact resolve eq57983 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57983
  have eq60067 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X4 (M.op X2 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1710 (M.op (M.op X0 X1) (M.op X2 X3)) (M.op X2 (M.op X1 X3)) X4
       have i₂ := eq1817 X2 X3 X0 X1
       grind)
    | exact superpose eq1817 eq1710
    | exact resolve eq1710 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60081 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 (M.op X1 X3))) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X4) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3569 (M.op (M.op X0 X1) (M.op X2 X3)) X4 (M.op X2 (M.op X1 X3))
       have i₂ := eq1817 X2 X3 X0 X1
       grind)
    | exact superpose eq1817 eq3569
    | exact resolve eq3569 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569
  have eq60086 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) x) (M.op x y)) = (M.op X0 (M.op (M.op X2 (M.op X1 X3)) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4590 (M.op (M.op X0 X1) (M.op X2 X3)) (M.op X2 (M.op X1 X3))
       have i₂ := eq1817 X2 X3 X0 X1
       grind)
    | exact superpose eq1817 eq4590
    | exact resolve eq4590 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4590
  have eq60087 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op X2 (M.op X1 X3)) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4593 (M.op (M.op X0 X1) (M.op X2 X3)) (M.op X2 (M.op X1 X3))
       have i₂ := eq1817 X2 X3 X0 X1
       grind)
    | exact superpose eq1817 eq4593
    | exact resolve eq4593 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817 eq4593
  have eq60094 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op X2 (M.op (M.op X1 X3) (σ y)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60087 X1 X1 X0 X3
       have i₂ := eq1659 X0 X1 (M.op X1 X3) sF3
       grind)
    | exact superpose eq1659 eq60087
    | exact resolve eq60087 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60087
  have eq60095 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) x) (M.op x y)) = (M.op X0 (M.op X2 (M.op (M.op X1 X3) y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60086 X0 X1 X2 X3
       have i₂ := eq1659 X2 X0 (M.op X1 X3) y
       grind)
    | exact superpose eq1659 eq60086
    | exact resolve eq60086 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60086
  have eq60098 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op X1 X3))) = (M.op (M.op (M.op (M.op X0 X1) x) x) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60081 X0 X1 X2 X3 x
       have i₂ := eq7499 (M.op X0 X1) (M.op X2 X3) x
       grind)
    | exact superpose eq7499 eq60081
    | exact resolve eq60081 eq7499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60081
  have eq60488 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (σ x)) (M.op (σ x) (σ y))) = (M.op X0 (M.op X2 (M.op (σ y) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60094 X0 X1 x X3
       have i₂ := eq1814 X0 (M.op X1 X3) sF3 x
       grind)
    | (have i₁ := eq60094 X0 X1 x X3
       have i₂ := eq1814 X0 sF3 (M.op X1 X3) x
       grind)
    | exact superpose eq1814 eq60094
    | exact resolve eq60094 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60094
  have eq60489 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) x) (M.op x y)) = (M.op X0 (M.op X2 (M.op y (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60095 X0 X1 X2 X3
       have i₂ := eq1814 X0 (M.op X1 X3) y X2
       grind)
    | (have i₁ := eq60095 X0 X1 X2 X3
       have i₂ := eq1814 X0 y (M.op X1 X3) X2
       grind)
    | exact superpose eq1814 eq60095
    | exact resolve eq60095 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60095
  have eq60808 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) (σ x)) (M.op (σ x) (σ y))) (M.op X2 X3)) = (M.op X0 (M.op X2 (M.op (σ y) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60488 X0 X1 X2 X3
       have i₂ := eq8039 (M.op X0 X1) (M.op X2 X3) sF2 sF4
       grind)
    | (have i₁ := eq60488 X0 X1 X2 X3
       have i₂ := eq8039 (M.op X0 X1) sF4 (M.op X2 X3) sF2
       grind)
    | exact superpose eq8039 eq60488
    | exact resolve eq60488 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60488
  have eq60809 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) x) (M.op x y)) (M.op X2 X3)) = (M.op X0 (M.op X2 (M.op y (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60489 X0 X1 X2 X3
       have i₂ := eq8039 (M.op X0 X1) (M.op X2 X3) x sF0
       grind)
    | (have i₁ := eq60489 X0 X1 X2 X3
       have i₂ := eq8039 (M.op X0 X1) sF0 (M.op X2 X3) x
       grind)
    | exact superpose eq8039 eq60489
    | exact resolve eq60489 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60489
  have eq61075 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op (σ y) (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) (σ x)) (σ x)) (M.op (σ y) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq19444 eq60808
    | exact resolve eq60808 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60808
  have eq61076 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op y (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) x) x) (M.op y (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq17981 eq60809
    | exact resolve eq60809 eq17981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60809
  have eq61278 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op (σ y) (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) x) x) (M.op (σ y) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61075 X0 X1 X2 X3
       have i₂ := eq18696 (M.op X0 X1) sF2 (M.op sF3 (M.op X2 X3))
       grind)
    | exact superpose eq18696 eq61075
    | exact resolve eq61075 eq18696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61075
  have eq61279 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op y (M.op X1 (M.op X2 X3)))) = (M.op X0 (M.op X2 (M.op y (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61076 X0 X1 X2 X3
       have i₂ := eq60098 X0 X1 y (M.op X2 X3)
       grind)
    | exact superpose eq60098 eq61076
    | exact resolve eq61076 eq60098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61076
  have eq61412 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op (σ y) (M.op X1 X3)))) = (M.op X0 (M.op (σ y) (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61278 X0 X1 X2 X3
       have i₂ := eq60098 X0 X1 sF3 (M.op X2 X3)
       grind)
    | exact superpose eq60098 eq61278
    | exact resolve eq61278 eq60098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61278
  have eq63901 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X2 X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 (M.op (σ y) X1)) X2) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21089 (M.op X1 (M.op X0 x)) X1
       have i₂ := eq1812 X0 X1 sF3 x
       grind)
    | (have i₁ := eq21089 (M.op X1 (M.op X2 x)) X1
       have i₂ := eq1812 sF3 X1 X2 x
       grind)
    | exact superpose eq1812 eq21089
    | exact resolve eq21089 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812 eq21089
  have eq64155 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X2 X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 (σ y)) (M.op X1 X2)) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq48793 eq63901
    | exact resolve eq63901 eq48793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63901
  have eq64265 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X2 X1)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 (σ y)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64155 X0 X2 X1 x
       have i₂ := eq6691 (M.op X0 sF3) X1 X2 x
       grind)
    | exact superpose eq6691 eq64155
    | exact resolve eq64155 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691 eq64155
  have eq64361 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op X2 X1)) = (M.op (M.op (M.op X0 (σ y)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64265 X0 X1 X2
       have i₂ := eq8039 X0 (M.op X2 X1) sF2 sF4
       grind)
    | (have i₁ := eq64265 X0 X1 X2
       have i₂ := eq8039 X0 sF4 (M.op X2 X1) sF2
       grind)
    | exact superpose eq8039 eq64265
    | exact resolve eq64265 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64265
  have eq64435 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (σ y) (M.op X2 X1))) = (M.op (M.op (M.op X0 (σ y)) X2) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq19444 eq64361
    | exact resolve eq64361 eq19444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19444 eq64361
  have eq64490 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) x) (M.op (σ y) (M.op X2 X1))) = (M.op (M.op (M.op X0 (σ y)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64435 X0 X1 X2
       have i₂ := eq18696 X0 sF2 (M.op sF3 (M.op X2 X1))
       grind)
    | exact superpose eq18696 eq64435
    | exact resolve eq64435 eq18696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18696 eq64435
  have eq64535 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op (σ y) (M.op (M.op (σ x) X1) X2))) X3) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq64490 eq46942
    | exact resolve eq46942 eq64490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46942 eq64490
  have eq64580 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (M.op (σ x) X1) X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64535 X0 X1 X2 X2
       have i₂ := eq8039 (M.op (M.op X0 x) x) (M.op sF3 (M.op (M.op sF2 X1) X2)) X2 sF4
       grind)
    | (have i₁ := eq64535 X0 X1 X2 X3
       have i₂ := eq8039 (M.op (M.op X0 x) x) sF4 (M.op sF3 (M.op (M.op sF2 X1) X2)) X3
       grind)
    | exact superpose eq8039 eq64535
    | exact resolve eq64535 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8039 eq64535
  have eq64615 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (M.op (σ x) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq48793 eq64580
    | exact resolve eq64580 eq48793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64580
  have eq64638 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op (σ x) (σ y))) (σ y)) (M.op (M.op (σ x) X1) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64615 X0 X1 X2 X3
       have i₂ := eq1659 (M.op sF2 X1) (M.op (M.op (M.op (M.op X0 x) x) sF4) sF3) X2 X3
       grind)
    | exact superpose eq1659 eq64615
    | exact resolve eq64615 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64615
  have eq64662 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op (σ x) (σ y))) (σ y)) (M.op (σ x) (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64638 X0 X2 X2 X3
       have i₂ := eq1659 sF2 (M.op (M.op (M.op (M.op X0 x) x) sF4) sF3) X2 (M.op X2 X3)
       grind)
    | exact superpose eq1659 eq64638
    | exact resolve eq64638 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64638
  have eq64684 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) x) (M.op (σ y) (M.op x (M.op (σ x) (σ y))))) (M.op (σ x) (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq31640 eq64662
    | exact resolve eq64662 eq31640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31640 eq64662
  have eq64710 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) x) (σ y)) (M.op (M.op x (M.op (σ x) (σ y))) (M.op (σ x) (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq48793 eq64684
    | exact resolve eq64684 eq48793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48793 eq64684
  have eq64733 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) x) (σ y)) (M.op x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X1 (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64710 X0 X1 X2 X3
       have i₂ := eq1659 x (M.op (M.op (M.op (M.op X0 x) x) x) sF3) sF4 (M.op sF2 (M.op X1 (M.op X2 X3)))
       grind)
    | exact superpose eq1659 eq64710
    | exact resolve eq64710 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64710
  have eq64752 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op (M.op (M.op (M.op X0 x) x) x) x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X1 (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq48118 eq64733
    | exact resolve eq64733 eq48118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48118 eq64733
  have eq64768 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X0 x) (M.op (σ y) (M.op x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X1 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64752 X0 X1 X2 X3
       have i₂ := eq60098 (M.op X0 x) x sF3 (M.op sF4 (M.op sF2 (M.op X1 (M.op X2 X3))))
       grind)
    | exact superpose eq60098 eq64752
    | exact resolve eq64752 eq60098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60098 eq64752
  have eq64780 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X0 x) (M.op x (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X1 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64768 X0 X1 X2 X3
       have i₂ := eq3372 sF3 (M.op sF4 (M.op sF2 (M.op X1 (M.op X2 X3)))) (M.op X0 x) x
       grind)
    | (have i₁ := eq64768 X0 X1 X2 X3
       have i₂ := eq3372 x (M.op sF4 (M.op sF2 (M.op X1 (M.op X2 X3)))) (M.op X0 x) sF3
       grind)
    | exact superpose eq3372 eq64768
    | exact resolve eq64768 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64768
  have eq64790 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X0 x) (M.op x (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq61412 eq64780
    | exact resolve eq64780 eq61412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64780
  have eq64795 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X0 x) (M.op x (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X1 (M.op X2 X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq39434 eq64790
    | exact resolve eq64790 eq39434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64790
  have eq64799 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X0 x) (M.op x (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X1 (M.op X2 X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq10070 eq64795
    | exact resolve eq64795 eq10070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64795
  have eq64801 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X0 x) (M.op x (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ y) (M.op (σ y) (M.op X1 (M.op X2 X3)))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq57628 eq64799
    | exact resolve eq64799 eq57628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57628 eq64799
  have eq64803 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X0 x) (M.op x (M.op (σ y) (M.op (σ y) (M.op X1 (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64801 X0 X1 X2 X3
       have i₂ := eq1815 x (M.op sF3 (M.op sF3 (M.op X1 (M.op X2 X3)))) sF1
       grind)
    | exact superpose eq1815 eq64801
    | exact resolve eq64801 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64801
  have eq64805 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X2 X1)) X3) = (M.op (M.op X0 x) (M.op x (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64803 X0 X1 X2 X3
       have i₂ := eq1815 x (M.op X1 (M.op X2 X3)) sF3
       grind)
    | exact superpose eq1815 eq64803
    | exact resolve eq64803 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64803
  have eq64905 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) x) (M.op y X2)) = (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X1 (M.op y X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52221 X0 X1 X2
       have i₂ := eq64805 (M.op X0 X1) X1 y X2
       grind)
    | exact superpose eq64805 eq52221
    | exact resolve eq52221 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52221
  have eq64946 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op X4 (M.op (σ x) (M.op (σ y) (M.op X3 (M.op X4 X2)))))) = (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq46306 X0 X1 X2 X3 X4
       have i₂ := eq64805 (M.op X0 X1) X1 X2 X3
       grind)
    | exact superpose eq64805 eq46306
    | exact resolve eq46306 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46306
  have eq64978 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 x) (M.op y (M.op X3 (M.op X0 (M.op x (M.op y X1)))))) = (M.op (M.op X2 x) (M.op x (M.op X1 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq48269 X0 X1 X2 X3
       have i₂ := eq64805 X2 X1 X0 X3
       grind)
    | exact superpose eq64805 eq48269
    | exact resolve eq48269 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48269
  have eq64992 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op x X0)) = (M.op (M.op X2 x) (M.op x (M.op (M.op X0 X1) (M.op x X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47830 X0 X1 X2 X3
       have i₂ := eq64805 X2 (M.op X0 X1) x X3
       grind)
    | exact superpose eq64805 eq47830
    | exact resolve eq47830 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47830
  have eq65005 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op X0 x) (M.op x (M.op (M.op X4 X3) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58324 X0 X1 X2 X3 X4
       have i₂ := eq64805 X0 (M.op X4 X3) X2 X1
       grind)
    | exact superpose eq64805 eq58324
    | exact resolve eq58324 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58324
  have eq65130 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) X5) (M.op X5 X4)) = (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X2 (M.op X1 (M.op X4 (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4775 X0 X1 X2 X3 X4 X5
       have i₂ := eq64805 (M.op X0 X1) X2 X1 (M.op X4 (M.op X2 X3))
       grind)
    | exact superpose eq64805 eq4775
    | exact resolve eq4775 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4775
  have eq65234 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op (σ (M.op x y)) (M.op y (M.op x (M.op y X0)))))) := by
    intro X0
    first
    | (have i₁ := eq46297 X0
       have i₂ := eq64805 (M.op sF1 x) sF1 y (M.op x (M.op y X0))
       grind)
    | exact superpose eq64805 eq46297
    | exact resolve eq46297 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46297
  have eq65484 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op y (M.op (σ (M.op x y)) (M.op x (M.op y X0)))))) := by
    intro X0
    first
    | (have i₁ := eq65234 X0
       have i₂ := eq58626 sF1 y (M.op x (M.op y X0)) (M.op (M.op sF1 x) x) x
       grind)
    | (have i₁ := eq65234 X0
       have i₂ := eq58626 y sF1 (M.op x (M.op y X0)) (M.op (M.op sF1 x) x) x
       grind)
    | exact superpose eq58626 eq65234
    | exact resolve eq65234 eq58626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65234
  have eq65701 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X4))) = (M.op (M.op X0 x) (M.op x (M.op X4 (M.op X3 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65005 X0 X1 X2 X3 X4
       have i₂ := eq1659 X4 x X3 (M.op X2 X1)
       grind)
    | exact superpose eq1659 eq65005
    | exact resolve eq65005 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65005
  have eq65714 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op x X0)) = (M.op (M.op X2 x) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64992 X0 X1 X2 X3
       have i₂ := eq60067 X2 x (M.op X0 X1) X3 x
       grind)
    | exact superpose eq60067 eq64992
    | exact resolve eq64992 eq60067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64992
  have eq66048 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op x (M.op x (M.op y (M.op (σ (M.op x y)) (M.op y X0)))))) := by
    intro X0
    first
    | (have i₁ := eq65484 X0
       have i₂ := eq61279 x sF1 x (M.op y X0)
       grind)
    | exact superpose eq61279 eq65484
    | exact resolve eq65484 eq61279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65484
  have eq66236 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op x X0)) = (M.op (M.op X2 x) (M.op X0 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65714 X0 X1 X2 X3
       have i₂ := eq1659 X0 (M.op X2 x) X1 X3
       grind)
    | exact superpose eq1659 eq65714
    | exact resolve eq65714 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65714
  have eq66527 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op y (M.op (σ (M.op x y)) (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq66048 X0
       have i₂ := eq64905 sF1 x (M.op sF1 (M.op y X0))
       grind)
    | exact superpose eq64905 eq66048
    | exact resolve eq66048 eq64905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64905 eq66048
  have eq66670 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 x) (M.op X0 (M.op X1 X3))) = (M.op (M.op X2 x) (M.op x (M.op X1 (M.op X3 (M.op x X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66236 X0 X1 X2 X3
       have i₂ := eq64805 X2 X1 X3 (M.op x X0)
       grind)
    | exact superpose eq64805 eq66236
    | exact resolve eq66236 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66236
  have eq66967 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op y (M.op y (M.op (σ (M.op x y)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq66527 x
       have i₂ := eq61279 (M.op (M.op sF1 x) x) sF1 y x
       grind)
    | exact superpose eq61279 eq66527
    | exact resolve eq66527 eq61279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61279 eq66527
  have eq67348 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq66967 X0
       have i₂ := eq1815 (M.op (M.op sF1 x) x) (M.op sF1 X0) y
       grind)
    | exact superpose eq1815 eq66967
    | exact resolve eq66967 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66967
  have eq68781 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) = (M.op X2 (M.op (M.op (σ x) (M.op X1 (σ y))) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq21620 eq1808
    | exact resolve eq1808 eq21620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21620
  have eq68916 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) = (M.op X2 (M.op (σ x) (M.op (M.op X1 (σ y)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68781 x X1 X1
       have i₂ := eq1659 sF2 X1 (M.op X1 sF3) x
       grind)
    | exact superpose eq1659 eq68781
    | exact resolve eq68781 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68781
  have eq69155 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) = (M.op X2 (M.op (σ x) (M.op X1 (M.op (σ y) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68916 x X0 X2
       have i₂ := eq1659 X0 sF2 sF3 x
       grind)
    | exact superpose eq1659 eq68916
    | exact resolve eq68916 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68916
  have eq72796 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op (M.op x y) y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq23547 eq4524
    | exact resolve eq4524 eq23547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23547
  have eq74410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x (M.op X0 y)) X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq26979 eq3467
    | exact resolve eq3467 eq26979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74529 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) (M.op y (M.op (M.op X0 y) X1))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74410 X0 X1 X2
       have i₂ := eq2831 (M.op X0 y) X1
       grind)
    | exact superpose eq2831 eq74410
    | exact resolve eq74410 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74410
  have eq74741 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) x) (M.op x (M.op (M.op (M.op X0 y) X1) (M.op y (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74529 X0 X1 X2
       have i₂ := eq64805 sF0 (M.op (M.op X0 y) X1) y (M.op X2 X2)
       grind)
    | exact superpose eq64805 eq74529
    | exact resolve eq74529 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74529
  have eq74924 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op X0 y) X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74741 X0 X1 X2
       have i₂ := eq60067 sF0 y (M.op (M.op X0 y) X1) (M.op X2 X2) x
       grind)
    | exact superpose eq60067 eq74741
    | exact resolve eq74741 eq60067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60067 eq74741
  have eq75095 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) y) (M.op (M.op X0 y) (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74924 X0 X2 X2
       have i₂ := eq1659 (M.op X0 y) (M.op sF0 y) X2 (M.op X2 X2)
       grind)
    | exact superpose eq1659 eq74924
    | exact resolve eq74924 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74924
  have eq75243 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) y) (M.op X0 (M.op y (M.op X1 (M.op X2 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75095 X0 X1 X2
       have i₂ := eq1659 X0 (M.op sF0 y) y (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq1659 eq75095
    | exact resolve eq75095 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75095
  have eq75363 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) X0) = (M.op (M.op (M.op x y) y) (M.op X0 (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq75243 X0 X1 x
       have i₂ := eq1677 X1 y x
       grind)
    | exact superpose eq1677 eq75243
    | exact resolve eq75243 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75243
  have eq85473 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X2) = (M.op x (M.op (M.op X2 (M.op X1 X0)) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26979 x (M.op x (M.op X2 X1))
       have i₂ := eq2176 sF0 X1 X2 x
       grind)
    | exact superpose eq2176 eq26979
    | exact resolve eq26979 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26979
  have eq85590 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X2) = (M.op x (M.op X2 (M.op (M.op X1 X0) y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85473 X0 X1 X2
       have i₂ := eq1659 X2 x (M.op X1 X0) y
       grind)
    | exact superpose eq1659 eq85473
    | exact resolve eq85473 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85473
  have eq86208 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X2) = (M.op x (M.op X2 (M.op y (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85590 X0 X1 X2
       have i₂ := eq1814 x (M.op X1 X0) y X2
       grind)
    | (have i₁ := eq85590 X0 X1 X2
       have i₂ := eq1814 x y (M.op X1 X0) X2
       grind)
    | exact superpose eq1814 eq85590
    | exact resolve eq85590 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814 eq85590
  have eq91386 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X2) = (M.op x (M.op (M.op y (M.op X1 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72796 (M.op y (M.op X2 X1)) X1
       have i₂ := eq2176 sF0 X1 X2 y
       grind)
    | exact superpose eq2176 eq72796
    | exact resolve eq72796 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72796
  have eq91826 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X2) = (M.op x (M.op y (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91386 X0 X1 X2
       have i₂ := eq1659 y x (M.op X1 X0) X2
       grind)
    | exact superpose eq1659 eq91386
    | exact resolve eq91386 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91386
  have eq91999 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X2) = (M.op x (M.op y (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91826 X0 X1 X2
       have i₂ := eq1659 X1 y X0 X2
       grind)
    | exact superpose eq1659 eq91826
    | exact resolve eq91826 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91826
  have eq92174 : ∀ X0 X1 X2 : G, (M.op x (M.op y (M.op X1 (M.op X0 X2)))) = (M.op x (M.op X2 (M.op y (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq91999 eq86208
    | exact resolve eq86208 eq91999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86208 eq91999
  have eq97884 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X1 (M.op x y))) X2) X4) (M.op y (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1920 (M.op X0 x) y X2 X4 X3
       have i₂ := eq4452 X0 X1
       grind)
    | exact superpose eq4452 eq1920
    | exact resolve eq1920 eq4452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4452
  have eq97931 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op y X1) X2)) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) X3) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1920 X0 X1 (M.op y X1) X3 X2
       have i₂ := eq1233 X0 X1
       grind)
    | exact superpose eq1233 eq1920
    | exact resolve eq1920 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq98070 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X0 X2))) = (M.op (M.op (M.op (M.op X3 X5) X4) X1) (M.op X5 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1920 X3 X5 X4 X1 (M.op X0 X2)
       have i₂ := eq4524 X0 X2 X1
       grind)
    | (have i₁ := eq1920 X3 X5 X4 X1 (M.op X0 X2)
       have i₂ := eq4524 X0 X1 X2
       grind)
    | exact superpose eq4524 eq1920
    | exact resolve eq1920 eq4524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4524
  have eq98215 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X3) X1) X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq525 (M.op (M.op (M.op X0 X3) X1) X3) X3 X2
       have i₂ := eq1920 X0 X3 X1 X3 X2
       grind)
    | exact superpose eq1920 eq525
    | exact resolve eq525 eq1920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98241 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 (M.op X2 X4)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq409 (M.op (M.op (M.op X0 X3) X1) X4) (M.op X3 (M.op X2 X4)) X5
       have i₂ := eq1920 X0 X3 X1 X4 X2
       grind)
    | exact superpose eq1920 eq409
    | exact resolve eq409 eq1920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq98296 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op (M.op X1 X2) (M.op X3 (M.op X2 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq98241 X0 X1 X2 X3 X4 x
       have i₂ := eq57418 X0 (M.op X1 X2) x (M.op X3 (M.op X2 X4))
       grind)
    | exact superpose eq57418 eq98241
    | exact resolve eq98241 eq57418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57418 eq98241
  have eq98458 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X0 X2))) = (M.op (M.op (M.op (M.op X3 X5) X4) X1) (M.op X5 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq98070 X0 X1 X2 X3 X4 X5
       have i₂ := eq1659 X0 X5 X1 X2
       grind)
    | exact superpose eq1659 eq98070
    | exact resolve eq98070 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98070
  have eq98588 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op y X1) X2)) = (M.op (M.op (M.op (M.op X0 x) x) (M.op y X3)) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq17981 eq97931
    | exact resolve eq97931 eq17981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97931
  have eq98627 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op X0 X1) x) (M.op x (M.op (M.op x y) (M.op X1 X2)))) X4) (M.op y (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq97884 X0 X2 X3 X3 X4
       have i₂ := eq64805 (M.op X0 X2) sF0 X2 X3
       grind)
    | exact superpose eq64805 eq97884
    | exact resolve eq97884 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97884
  have eq98703 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op X2 (M.op X3 (M.op X2 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq98296 X0 X1 X2 X3 X4
       have i₂ := eq1659 X1 (M.op (M.op X0 x) x) X2 (M.op X3 (M.op X2 X4))
       grind)
    | exact superpose eq1659 eq98296
    | exact resolve eq98296 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98296
  have eq98951 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op y X1) X2)) = (M.op (M.op (M.op (M.op X0 x) x) x) (M.op x (M.op X3 (M.op y (M.op X1 (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq98588 X0 X1 X2 X3
       have i₂ := eq64805 (M.op (M.op X0 x) x) X3 y (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq64805 eq98588
    | exact resolve eq98588 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98588
  have eq98985 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) (M.op x (M.op (M.op (M.op x y) (M.op X1 X2)) (M.op x X4)))) (M.op y (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq98627 X0 X1 X2 X3 X3
       have i₂ := eq64805 (M.op (M.op X0 X1) x) (M.op sF0 (M.op X1 X2)) x X3
       grind)
    | exact superpose eq64805 eq98627
    | exact resolve eq98627 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98627
  have eq99059 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq98703 X0 X1 x X3 X4
       have i₂ := eq8170 X3 x X4 X1
       grind)
    | exact superpose eq8170 eq98703
    | exact resolve eq98703 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98703
  have eq99271 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op y X1) X2)) = (M.op X0 (M.op x (M.op x (M.op X3 (M.op y (M.op X1 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq98951 X0 X1 X2 X3
       have i₂ := eq98215 X0 x (M.op x (M.op X3 (M.op y (M.op X1 (M.op X2 X3))))) x
       grind)
    | exact superpose eq98215 eq98951
    | exact resolve eq98951 eq98215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98951
  have eq99306 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op X0 X1) x) x) x) (M.op x (M.op (M.op (M.op (M.op x y) (M.op X1 X2)) (M.op x X4)) (M.op x (M.op y (M.op X3 X4)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq98985 X0 X1 X2 X3 X4
       have i₂ := eq64805 (M.op (M.op (M.op X0 X1) x) x) (M.op (M.op sF0 (M.op X1 X2)) (M.op x X4)) x (M.op y (M.op X3 X4))
       grind)
    | exact superpose eq64805 eq98985
    | exact resolve eq98985 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98985
  have eq99423 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X1 (M.op X2 X3)))) = (M.op (M.op (M.op X0 x) x) (M.op (σ y) (M.op (σ x) (M.op X4 (M.op (σ x) (M.op (σ y) (M.op X3 (M.op X4 X2)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq64946 X0 X1 X2 X3 X4
       have i₂ := eq99059 X0 sF3 sF2 (M.op X4 (M.op sF2 (M.op sF3 (M.op X3 (M.op X4 X2)))))
       grind)
    | exact superpose eq99059 eq64946
    | exact resolve eq64946 eq99059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64946
  have eq99613 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op y X1) X2)) = (M.op X0 (M.op X3 (M.op y (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99271 X0 X1 X2 X3
       have i₂ := eq1815 X0 (M.op X3 (M.op y (M.op X1 (M.op X2 X3)))) x
       grind)
    | exact superpose eq1815 eq99271
    | exact resolve eq99271 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99271
  have eq99641 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op x (M.op (M.op (M.op (M.op x y) (M.op X1 X2)) (M.op x X4)) (M.op y (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq99306 X0 X1 X2 X3 X4
       have i₂ := eq98458 (M.op (M.op sF0 (M.op X1 X2)) (M.op x X4)) x (M.op y (M.op X3 X4)) (M.op X0 X1) x x
       grind)
    | exact superpose eq98458 eq99306
    | exact resolve eq99306 eq98458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99306
  have eq99729 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X1 (M.op X2 X3)))) = (M.op (M.op (M.op X0 x) x) (M.op (σ x) (M.op (σ y) (M.op X4 (M.op (σ x) (M.op (σ y) (M.op X3 (M.op X4 X2)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq99423 X0 X1 X2 X3 X4
       have i₂ := eq3372 sF3 (M.op X4 (M.op sF2 (M.op sF3 (M.op X3 (M.op X4 X2))))) (M.op (M.op X0 x) x) sF2
       grind)
    | (have i₁ := eq99423 X0 X1 X2 X3 X4
       have i₂ := eq3372 sF2 (M.op X4 (M.op sF2 (M.op sF3 (M.op X3 (M.op X4 X2))))) (M.op (M.op X0 x) x) sF3
       grind)
    | exact superpose eq3372 eq99423
    | exact resolve eq99423 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99423
  have eq99883 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op y (M.op X1 X2))) = (M.op X0 (M.op X3 (M.op y (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99613 X0 X1 X2 X3
       have i₂ := eq1659 y X0 X1 X2
       grind)
    | exact superpose eq1659 eq99613
    | exact resolve eq99613 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99613
  have eq99908 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op x (M.op y (M.op (M.op (M.op (M.op x y) (M.op X1 X2)) (M.op x X4)) (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq99641 X0 X1 X2 X3 X4
       have i₂ := eq58626 (M.op (M.op sF0 (M.op X1 X2)) (M.op x X4)) y (M.op X3 X4) (M.op X0 X1) x
       grind)
    | (have i₁ := eq99641 X0 X1 X2 X3 X4
       have i₂ := eq58626 y (M.op (M.op sF0 (M.op X1 X2)) (M.op x X4)) (M.op X3 X4) (M.op X0 X1) x
       grind)
    | exact superpose eq58626 eq99641
    | exact resolve eq99641 eq58626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99641
  have eq99984 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X1 (M.op X2 X3)))) = (M.op (M.op (M.op X0 x) x) (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op X4 (M.op (σ y) (M.op X3 (M.op X4 X2)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq61412 eq99729
    | exact resolve eq99729 eq61412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99729
  have eq100108 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op x (M.op X4 (M.op y (M.op (M.op (M.op (M.op x y) (M.op X1 X2)) (M.op x X4)) X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq99908 X0 X1 X2 X0 X2
       have i₂ := eq92174 X0 (M.op (M.op sF0 (M.op X1 X2)) (M.op x X2)) X2
       grind)
    | exact superpose eq92174 eq99908
    | exact resolve eq99908 eq92174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92174 eq99908
  have eq100166 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X1 (M.op X2 X3)))) = (M.op (M.op (M.op X0 x) x) (M.op (σ y) (M.op X4 (M.op (σ y) (M.op X3 (M.op X4 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq99984 X0 X1 X2 X3 X4
       have i₂ := eq1815 (M.op (M.op X0 x) x) (M.op sF3 (M.op X4 (M.op sF3 (M.op X3 (M.op X4 X2))))) sF2
       grind)
    | exact superpose eq1815 eq99984
    | exact resolve eq99984 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99984
  have eq100261 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op x (M.op X4 (M.op y (M.op (M.op (M.op x y) (M.op X1 X2)) (M.op (M.op x X4) X3)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100108 X0 X1 X2 X3 X4
       have i₂ := eq1659 (M.op sF0 (M.op X1 X2)) y (M.op x X4) X3
       grind)
    | exact superpose eq1659 eq100108
    | exact resolve eq100108 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100108
  have eq100315 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X1 (M.op X2 X3)))) = (M.op (M.op (M.op X0 x) x) (M.op X4 (M.op X3 (M.op X4 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100166 X0 X1 X2 X3 X0
       have i₂ := eq8170 X0 sF3 (M.op X3 (M.op X0 X2)) (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq8170 eq100166
    | exact resolve eq100166 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100166
  have eq100393 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op x (M.op X4 (M.op y (M.op (M.op x y) (M.op (M.op X1 X2) (M.op (M.op x X4) X3))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100261 X0 X1 X2 X3 X4
       have i₂ := eq1659 sF0 y (M.op X1 X2) (M.op (M.op x X4) X3)
       grind)
    | exact superpose eq1659 eq100261
    | exact resolve eq100261 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100261
  have eq100434 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 x) x) (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq100315 X0 X1 X2 X3 x
       have i₂ := eq8170 X3 x X2 (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq8170 eq100315
    | exact resolve eq100315 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100315
  have eq100509 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op x (M.op X4 (M.op y (M.op x (M.op y (M.op (M.op X1 X2) (M.op (M.op x X4) X3)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1654 eq100393
    | exact resolve eq100393 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100393
  have eq100604 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op x (M.op X4 (M.op x (M.op y (M.op y (M.op (M.op X1 X2) (M.op (M.op x X4) X3)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100509 X0 X1 X2 X3 X4
       have i₂ := eq58626 y x (M.op y (M.op (M.op X1 X2) (M.op (M.op x X4) X3))) x X4
       grind)
    | (have i₁ := eq100509 X0 X1 X2 X3 X4
       have i₂ := eq58626 x y (M.op y (M.op (M.op X1 X2) (M.op (M.op x X4) X3))) x X4
       grind)
    | exact superpose eq58626 eq100509
    | exact resolve eq100509 eq58626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100509
  have eq100676 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op X4 (M.op y (M.op y (M.op (M.op X1 X2) (M.op (M.op x X4) X3)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100604 X0 X1 X2 X3 X4
       have i₂ := eq8170 X4 x (M.op y (M.op y (M.op (M.op X1 X2) (M.op (M.op x X4) X3)))) (M.op X0 X1)
       grind)
    | exact superpose eq8170 eq100604
    | exact resolve eq100604 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100604
  have eq100738 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op X4 (M.op (M.op X1 X2) (M.op (M.op x X4) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100676 X0 X1 X2 X3 X4
       have i₂ := eq1815 X4 (M.op (M.op X1 X2) (M.op (M.op x X4) X3)) y
       grind)
    | exact superpose eq1815 eq100676
    | exact resolve eq100676 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100676
  have eq100791 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op X4 (M.op X1 (M.op X2 (M.op (M.op x X4) X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100738 X0 X1 X2 X3 X4
       have i₂ := eq1659 X1 X4 X2 (M.op (M.op x X4) X3)
       grind)
    | exact superpose eq1659 eq100738
    | exact resolve eq100738 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100738
  have eq100827 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 x) (M.op X2 X3)) = (M.op (M.op X0 X1) (M.op X4 (M.op X1 (M.op X2 (M.op x (M.op X4 X3)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq100791 X0 X1 X2 X3 X4
       have i₂ := eq1659 x X2 X4 X3
       grind)
    | exact superpose eq1659 eq100791
    | exact resolve eq100791 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100791
  have eq101213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq361
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq361
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq361 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq101243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101213
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101213
    | exact resolve eq101213 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101213
  have eq101252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq101243
    | exact resolve eq101243 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101243
  have eq101259 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq101252
       have r₂ := eq27
       grind)
    | exact resolve eq101252 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101252
  have eq101266 : (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101259
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101259
    | exact resolve eq101259 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101259
  have eq101267 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq101266
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101266
    | exact resolve eq101266 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101266
  have eq101291 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq101267 eq409
    | exact resolve eq409 eq101267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101267
  have eq101340 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39434 eq101291
    | exact resolve eq101291 eq39434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101291
  have eq101367 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (M.op (σ x) (M.op (σ y) X0)) (M.op (σ (M.op x y)) (M.op (σ y) X0))))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq101340 X0
       have i₂ := eq64805 sF1 (M.op sF2 (M.op sF3 X0)) sF1 (M.op sF3 X0)
       grind)
    | exact superpose eq64805 eq101340
    | exact resolve eq101340 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101340
  have eq101383 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0))))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq101367 x
       have i₂ := eq65701 sF1 x sF3 sF1 (M.op sF2 (M.op sF3 x))
       grind)
    | exact superpose eq65701 eq101367
    | exact resolve eq101367 eq65701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65701 eq101367
  have eq101394 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ y) X0))))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq61412 eq101383
    | exact resolve eq101383 eq61412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61412 eq101383
  have eq101403 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) X0))))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10070 eq101394
    | exact resolve eq101394 eq10070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10070 eq101394
  have eq101408 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) (M.op (σ x) X0))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq101403 x
       have i₂ := eq1815 sF2 x sF3
       grind)
    | exact superpose eq1815 eq101403
    | exact resolve eq101403 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101403
  have eq101412 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37146 eq101408
    | exact resolve eq101408 eq37146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37146 eq101408
  have eq101442 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) (M.op X0 y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1710 y y X0
       have i₂ := eq101412
       grind)
    | exact superpose eq101412 eq1710
    | exact resolve eq1710 eq101412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101412
  have eq101468 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2055 eq101442
    | exact resolve eq101442 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055 eq101442
  have eq101508 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq101468 eq2165
    | exact resolve eq2165 eq101468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101516 : (τ (σ y)) = (M.op x (M.op x (τ (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq101468 eq37543
    | exact resolve eq37543 eq101468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37543 eq101468
  have eq101525 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq39 eq101516
    | exact resolve eq101516 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101516
  have eq101528 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq101508
    | (have j0 := eq101508 X0
       grind)
    | exact resolve eq101508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101508
  have eq101529 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101525
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101525
    | exact resolve eq101525 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101525
  have eq103605 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq101528 eq50707
    | exact resolve eq50707 eq101528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50707 eq101528
  have eq103732 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq103605
       have i₂ := eq1808 sF2 sF4 sF3
       grind)
    | (have i₁ := eq103605
       have i₂ := eq1808 sF2 sF3 sF4
       grind)
    | exact superpose eq1808 eq103605
    | exact resolve eq103605 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808 eq103605
  have eq103800 : (M.op x (M.op x x)) = (τ (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ y))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3390 eq103732
    | exact resolve eq103732 eq3390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390 eq103732
  have eq103852 : (τ (M.op (σ x) (σ x))) = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq103800
       have i₂ := eq1677 sF2 sF2 sF3
       grind)
    | exact superpose eq1677 eq103800
    | exact resolve eq103800 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103800
  have eq103895 : (M.op (τ (σ x)) (τ (σ x))) = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq103852
       have i₂ := eq236 sF2
       grind)
    | exact superpose eq236 eq103852
    | exact resolve eq103852 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq103852
  have eq103917 : (M.op x x) = (M.op x (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq103895
    | exact resolve eq103895 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103895
  have eq106550 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X0 X3) x) x) x) (M.op X4 X5)) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op X1 X2)) x) (M.op x (M.op (M.op x (M.op X3 (M.op X2 X1))) (M.op X5 X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq100434 (M.op (M.op X0 X3) x) (M.op x (M.op X3 (M.op X2 X1))) X5 X4
       have i₂ := eq100434 X0 X3 X2 X1
       grind)
    | exact superpose eq100434 eq100434
    | exact resolve eq100434 eq100434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107255 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X0 X3) x) x) x) (M.op X4 X5)) = (M.op (M.op (M.op (M.op (M.op X0 x) x) x) x) (M.op x (M.op (M.op X1 X2) (M.op x (M.op (M.op x (M.op X3 (M.op X2 X1))) (M.op X5 X4)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq106550 X0 X1 X2 X3 X4 X5
       have i₂ := eq99059 (M.op (M.op X0 x) x) x (M.op X1 X2) (M.op x (M.op (M.op x (M.op X3 (M.op X2 X1))) (M.op X5 X4)))
       grind)
    | exact superpose eq99059 eq106550
    | exact resolve eq106550 eq99059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106550
  have eq107718 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X0 X3) x) x) x) (M.op X4 X5)) = (M.op (M.op X0 x) (M.op x (M.op (M.op X1 X2) (M.op (M.op x (M.op X3 (M.op X2 X1))) (M.op X5 X4))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq107255 X0 X1 X2 X3 X4 X5
       have i₂ := eq98458 (M.op X1 X2) x (M.op (M.op x (M.op X3 (M.op X2 X1))) (M.op X5 X4)) (M.op X0 x) x x
       grind)
    | exact superpose eq98458 eq107255
    | exact resolve eq107255 eq98458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98458 eq107255
  have eq108096 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X0 X3) x) x) x) (M.op X4 X5)) = (M.op (M.op X0 x) (M.op x (M.op X1 (M.op X2 (M.op (M.op x (M.op X3 (M.op X2 X1))) (M.op X5 X4)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq107718 X0 X1 X2 X3 X4 X5
       have i₂ := eq1659 X1 x X2 (M.op (M.op x (M.op X3 (M.op X2 X1))) (M.op X5 X4))
       grind)
    | exact superpose eq1659 eq107718
    | exact resolve eq107718 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107718
  have eq108411 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X0 X3) x) x) x) (M.op X4 X5)) = (M.op (M.op X0 x) (M.op x (M.op X1 (M.op X2 (M.op x (M.op (M.op X3 (M.op X2 X1)) (M.op X5 X4))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq108096 X0 X1 X2 X3 X4 X5
       have i₂ := eq1659 x X2 (M.op X3 (M.op X2 X1)) (M.op X5 X4)
       grind)
    | exact superpose eq1659 eq108096
    | exact resolve eq108096 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108096
  have eq108682 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X0 X3) x) x) x) (M.op X4 X5)) = (M.op (M.op X0 x) (M.op x (M.op X1 (M.op X2 (M.op x (M.op X3 (M.op (M.op X2 X1) (M.op X5 X4)))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq108411 X0 X1 X2 X3 X4 X5
       have i₂ := eq1659 X3 x (M.op X2 X1) (M.op X5 X4)
       grind)
    | exact superpose eq1659 eq108411
    | exact resolve eq108411 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108411
  have eq108905 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X0 X3) x) x) x) (M.op X4 X5)) = (M.op (M.op X0 x) (M.op x (M.op X1 (M.op X2 (M.op x (M.op X3 (M.op X2 (M.op X1 (M.op X5 X4))))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq108682 X0 X1 X2 X3 X4 X5
       have i₂ := eq1659 X2 X3 X1 (M.op X5 X4)
       grind)
    | exact superpose eq1659 eq108682
    | exact resolve eq108682 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108682
  have eq109091 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 x) (M.op x (M.op X1 (M.op X2 (M.op x (M.op X3 (M.op X2 (M.op X1 (M.op X5 X4))))))))) = (M.op (M.op X0 X3) (M.op x (M.op X4 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq108905 X0 X1 X2 X3 X4 X5
       have i₂ := eq98215 (M.op X0 X3) x (M.op X4 X5) x
       grind)
    | exact superpose eq98215 eq108905
    | exact resolve eq108905 eq98215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108905
  have eq138360 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X2 X1) X3)) = (M.op (M.op (M.op (M.op X0 X1) X4) x) (M.op x (M.op X5 (M.op X4 (M.op X3 (M.op X5 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq65130 (M.op X0 X1) X4 X5 X2 X3 (M.op X2 X1)
       have i₂ := eq1710 X0 X1 X2
       grind)
    | exact superpose eq1710 eq65130
    | exact resolve eq65130 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138367 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) = (M.op (M.op (M.op (M.op X0 x) x) (M.op X1 X2)) (M.op (M.op x (M.op X3 (M.op X2 X1))) X4)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq65130 (M.op X0 X3) X5 X6 x X4 (M.op x (M.op X3 (M.op X2 X1)))
       have i₂ := eq100434 X0 X3 X2 X1
       grind)
    | exact superpose eq100434 eq65130
    | exact resolve eq65130 eq100434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100434
  have eq139258 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 (M.op X6 X3)) (M.op (M.op X0 X4) X6)) = (M.op (M.op X5 X7) (M.op X7 (M.op (M.op (M.op X0 X1) x) (M.op x (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4)))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq2176 X5 (M.op X6 X3) (M.op (M.op X0 X4) X6) X7
       have i₂ := eq65130 X0 X1 X2 X4 X3 X6
       grind)
    | exact superpose eq65130 eq2176
    | exact resolve eq2176 eq65130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139290 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 (M.op (M.op X0 X6) x)) (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2176 X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1)))) x (M.op (M.op X0 X6) x)
       have i₂ := eq65130 X0 X6 X5 X1 X3 X2
       grind)
    | exact superpose eq65130 eq2176
    | exact resolve eq2176 eq65130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176 eq65130
  have eq139383 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 x) (M.op x (M.op x (M.op (M.op X0 X6) (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq139290 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq64805 X4 x (M.op X0 X6) (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3))
       grind)
    | exact superpose eq64805 eq139290
    | exact resolve eq139290 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139290
  have eq139414 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 (M.op X6 X3)) (M.op (M.op X0 X4) X6)) = (M.op (M.op X5 X7) (M.op X7 (M.op x (M.op (M.op (M.op X0 X1) x) (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4)))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq139258 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq58626 (M.op (M.op X0 X1) x) x (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4)))) (M.op X5 X7) X7
       grind)
    | (have i₁ := eq139258 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq58626 x (M.op (M.op X0 X1) x) (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4)))) (M.op X5 X7) X7
       grind)
    | exact superpose eq58626 eq139258
    | exact resolve eq139258 eq58626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139258
  have eq140196 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) = (M.op (M.op (M.op (M.op X0 x) x) x) (M.op (M.op X1 X2) (M.op x (M.op (M.op x (M.op X3 (M.op X2 X1))) X4)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq138367 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq99059 (M.op X0 x) (M.op X1 X2) x (M.op (M.op x (M.op X3 (M.op X2 X1))) X4)
       grind)
    | exact superpose eq99059 eq138367
    | exact resolve eq138367 eq99059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99059 eq138367
  have eq140203 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X2 (M.op X1 X3))) = (M.op (M.op (M.op (M.op X0 X1) X4) x) (M.op x (M.op X5 (M.op X4 (M.op X3 (M.op X5 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq138360 X0 X1 X2 X3 X4 X5
       have i₂ := eq1659 X2 X0 X1 X3
       grind)
    | exact superpose eq1659 eq138360
    | exact resolve eq138360 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138360
  have eq140417 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 x) (M.op (M.op X0 X6) (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq139383 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq1822 X4 x (M.op (M.op X0 X6) (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3))) x
       grind)
    | exact superpose eq1822 eq139383
    | exact resolve eq139383 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139383
  have eq140446 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 (M.op X6 X3)) (M.op (M.op X0 X4) X6)) = (M.op (M.op X5 X7) (M.op X7 (M.op x (M.op (M.op X0 X1) (M.op x (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4))))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq139414 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq1659 (M.op X0 X1) x x (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4))))
       grind)
    | exact superpose eq1659 eq139414
    | exact resolve eq139414 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139414
  have eq141138 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) = (M.op X0 (M.op x (M.op (M.op X1 X2) (M.op x (M.op (M.op x (M.op X3 (M.op X2 X1))) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq140196 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq98215 X0 x (M.op (M.op X1 X2) (M.op x (M.op (M.op x (M.op X3 (M.op X2 X1))) X4))) x
       grind)
    | exact superpose eq98215 eq140196
    | exact resolve eq140196 eq98215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98215 eq140196
  have eq141348 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 x) (M.op X0 (M.op X6 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq140417 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq1659 X0 (M.op X4 x) X6 (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3))
       grind)
    | exact superpose eq1659 eq140417
    | exact resolve eq140417 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140417
  have eq141375 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 (M.op X6 X3)) (M.op (M.op X0 X4) X6)) = (M.op (M.op X5 X7) (M.op X7 (M.op x (M.op x (M.op (M.op X0 X1) (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4))))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq140446 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq58626 (M.op X0 X1) x (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4)))) X7 x
       grind)
    | (have i₁ := eq140446 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq58626 x (M.op X0 X1) (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4)))) X7 x
       grind)
    | exact superpose eq58626 eq140446
    | exact resolve eq140446 eq58626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140446
  have eq141951 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) = (M.op X0 (M.op x (M.op x (M.op (M.op X1 X2) (M.op (M.op x (M.op X3 (M.op X2 X1))) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq141138 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq58626 (M.op X1 X2) x (M.op (M.op x (M.op X3 (M.op X2 X1))) X4) X0 x
       grind)
    | (have i₁ := eq141138 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq58626 x (M.op X1 X2) (M.op (M.op x (M.op X3 (M.op X2 X1))) X4) X0 x
       grind)
    | exact superpose eq58626 eq141138
    | exact resolve eq141138 eq58626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141138
  have eq142145 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 x) (M.op X0 (M.op X6 (M.op X2 (M.op (M.op (M.op X0 X1) X2) X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq141348 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq58626 (M.op (M.op X0 X1) X2) X2 X3 X0 X6
       grind)
    | (have i₁ := eq141348 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq58626 X2 (M.op (M.op X0 X1) X2) X3 X0 X6
       grind)
    | exact superpose eq58626 eq141348
    | exact resolve eq141348 eq58626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58626 eq141348
  have eq142171 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 (M.op X6 X3)) (M.op (M.op X0 X4) X6)) = (M.op (M.op X5 X7) (M.op X7 (M.op (M.op X0 X1) (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq141375 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq1815 X7 (M.op (M.op X0 X1) (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4))))) x
       grind)
    | exact superpose eq1815 eq141375
    | exact resolve eq141375 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141375
  have eq142648 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) = (M.op X0 (M.op (M.op X1 X2) (M.op (M.op x (M.op X3 (M.op X2 X1))) X4))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq141951 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq1815 X0 (M.op (M.op X1 X2) (M.op (M.op x (M.op X3 (M.op X2 X1))) X4)) x
       grind)
    | exact superpose eq1815 eq141951
    | exact resolve eq141951 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141951
  have eq142821 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 x) (M.op X0 (M.op X6 (M.op X2 (M.op (M.op X0 X1) (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq142145 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq1659 (M.op X0 X1) X2 X2 X3
       grind)
    | exact superpose eq1659 eq142145
    | exact resolve eq142145 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142145
  have eq142847 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 (M.op X6 X3)) (M.op (M.op X0 X4) X6)) = (M.op (M.op X5 X7) (M.op X7 (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4)))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq142171 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq1659 X0 X7 X1 (M.op X2 (M.op X1 (M.op X3 (M.op X2 X4))))
       grind)
    | exact superpose eq1659 eq142171
    | exact resolve eq142171 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142171
  have eq143224 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) = (M.op X0 (M.op X1 (M.op X2 (M.op (M.op x (M.op X3 (M.op X2 X1))) X4)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq142648 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq1659 X1 X0 X2 (M.op (M.op x (M.op X3 (M.op X2 X1))) X4)
       grind)
    | exact superpose eq1659 eq142648
    | exact resolve eq142648 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142648
  have eq143374 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 x) (M.op X0 (M.op X6 (M.op (M.op X0 X1) X3)))) := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq142821 X0 X1 x X3 X4 X5 X6
       have i₂ := eq8170 (M.op X0 X1) x X3 X6
       grind)
    | exact superpose eq8170 eq142821
    | exact resolve eq142821 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142821
  have eq143399 : ∀ X0 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 (M.op X6 X3)) (M.op (M.op X0 X4) X6)) = (M.op (M.op X5 X7) (M.op X7 (M.op X0 (M.op X2 (M.op X3 (M.op X2 X4)))))) := by
    intro X0 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq142847 X0 x X2 X3 X4 X5 X6 X7
       have i₂ := eq8170 X2 x (M.op X3 (M.op X2 X4)) X0
       grind)
    | exact superpose eq8170 eq142847
    | exact resolve eq142847 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142847
  have eq143716 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) = (M.op X0 (M.op X1 (M.op X2 (M.op x (M.op (M.op X3 (M.op X2 X1)) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq143224 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq1659 x X2 (M.op X3 (M.op X2 X1)) X4
       grind)
    | exact superpose eq1659 eq143224
    | exact resolve eq143224 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143224
  have eq143846 : ∀ X0 X1 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 x) (M.op X0 (M.op X6 (M.op X0 (M.op X1 X3))))) := by
    intro X0 X1 X3 X4 X5 X6
    first
    | (have i₁ := eq143374 X0 X1 X3 X4 X5 X6
       have i₂ := eq1659 X0 X6 X1 X3
       grind)
    | exact superpose eq1659 eq143374
    | exact resolve eq143374 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143374
  have eq143870 : ∀ X0 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 (M.op X6 X3)) (M.op (M.op X0 X4) X6)) = (M.op (M.op X5 X7) (M.op X7 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq143399 X0 x X3 X4 X5 X6 X7
       have i₂ := eq8170 X3 x X4 X0
       grind)
    | exact superpose eq8170 eq143399
    | exact resolve eq143399 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143399
  have eq144110 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) = (M.op X0 (M.op X1 (M.op X2 (M.op x (M.op X3 (M.op (M.op X2 X1) X4)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq143716 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq1659 X3 x (M.op X2 X1) X4
       grind)
    | exact superpose eq1659 eq143716
    | exact resolve eq143716 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143716
  have eq144219 : ∀ X1 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) x) = (M.op (M.op X4 x) (M.op X6 (M.op X1 X3))) := by
    intro X1 X3 X4 X5 X6
    first
    | (have i₁ := eq143846 x X1 X3 X4 X5 X6
       have i₂ := eq8170 X6 x (M.op X1 X3) (M.op X4 x)
       grind)
    | exact superpose eq8170 eq143846
    | exact resolve eq143846 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8170 eq143846
  have eq144242 : ∀ X0 X3 X4 X5 X6 X7 : G, (M.op (M.op X5 X7) (M.op X7 (M.op X0 (M.op X3 X4)))) = (M.op (M.op X5 x) (M.op x (M.op X3 (M.op X6 (M.op (M.op X0 X4) X6))))) := by
    intro X0 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq143870 X0 X3 X4 X5 X6 X7
       have i₂ := eq64805 X5 X3 X6 (M.op (M.op X0 X4) X6)
       grind)
    | exact superpose eq64805 eq143870
    | exact resolve eq143870 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143870
  have eq144407 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op X1 (M.op X2 (M.op x (M.op X3 (M.op X2 (M.op X1 X4))))))) = (M.op (M.op (M.op (M.op X0 X3) X5) x) (M.op x (M.op X6 (M.op X5 (M.op X4 (M.op X6 x)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq144110 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq1659 X2 X3 X1 X4
       grind)
    | exact superpose eq1659 eq144110
    | exact resolve eq144110 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659 eq144110
  have eq144495 : ∀ X1 X3 X4 X5 X6 : G, (M.op (M.op X4 x) (M.op X6 (M.op X1 X3))) = (M.op (M.op X4 x) (M.op x (M.op (M.op X6 (M.op X3 (M.op X5 X1))) (M.op X5 x)))) := by
    intro X1 X3 X4 X5 X6
    first
    | (have i₁ := eq144219 X1 X3 X4 X5 X6
       have i₂ := eq64805 X4 (M.op X6 (M.op X3 (M.op X5 X1))) X5 x
       grind)
    | exact superpose eq64805 eq144219
    | exact resolve eq144219 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144219
  have eq144516 : ∀ X0 X3 X4 X5 X7 : G, (M.op (M.op X5 X7) (M.op X7 (M.op X0 (M.op X3 X4)))) = (M.op (M.op X5 x) (M.op x (M.op X3 (M.op X0 X4)))) := by
    intro X0 X3 X4 X5 X7
    first
    | (have i₁ := eq144242 X0 X3 X4 X5 x X7
       have i₂ := eq525 X3 x (M.op X0 X4)
       grind)
    | exact superpose eq525 eq144242
    | exact resolve eq144242 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144242
  have eq144638 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 (M.op x (M.op X3 (M.op X2 (M.op X1 X4))))))) = (M.op X0 (M.op x (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq144407 X0 X1 X2 X3 X4 x x
       have i₂ := eq140203 X0 X3 x X4 x x
       grind)
    | exact superpose eq140203 eq144407
    | exact resolve eq144407 eq140203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140203 eq144407
  have eq144713 : ∀ X1 X3 X4 X5 X6 : G, (M.op (M.op X4 x) (M.op X6 (M.op X1 X3))) = (M.op (M.op X4 x) (M.op y (M.op x (M.op X5 (M.op x (M.op y (M.op X6 (M.op X3 (M.op X5 X1))))))))) := by
    intro X1 X3 X4 X5 X6
    first
    | (have i₁ := eq144495 X1 X3 X4 X5 X6
       have i₂ := eq64978 X5 (M.op X6 (M.op X3 (M.op X5 X1))) X4 x
       grind)
    | exact superpose eq64978 eq144495
    | exact resolve eq144495 eq64978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64978 eq144495
  have eq144839 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op x (M.op X4 X5))) = (M.op (M.op X0 x) (M.op x (M.op x (M.op X3 (M.op X5 X4))))) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq109091 X0 x x X3 X4 X5
       have i₂ := eq144638 x x x X3 (M.op X5 X4)
       grind)
    | exact superpose eq144638 eq109091
    | exact resolve eq109091 eq144638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109091 eq144638
  have eq144909 : ∀ X1 X3 X4 X5 X6 : G, (M.op (M.op X4 x) (M.op X5 (M.op X6 (M.op X3 (M.op X5 X1))))) = (M.op (M.op X4 x) (M.op X6 (M.op X1 X3))) := by
    intro X1 X3 X4 X5 X6
    first
    | (have i₁ := eq144713 X1 X3 X4 X5 X6
       have i₂ := eq100827 X4 x X5 (M.op X6 (M.op X3 (M.op X5 X1))) y
       grind)
    | exact superpose eq100827 eq144713
    | exact resolve eq144713 eq100827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100827 eq144713
  have eq145001 : ∀ X0 X3 X4 X5 : G, (M.op (M.op X0 X3) (M.op x (M.op X4 X5))) = (M.op (M.op X0 x) (M.op X3 (M.op X5 X4))) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq144839 X0 X3 X4 X5
       have i₂ := eq1822 X0 x (M.op X3 (M.op X5 X4)) x
       grind)
    | exact superpose eq1822 eq144839
    | exact resolve eq144839 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144839
  have eq167318 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) (M.op X0 (M.op x x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1710 x (M.op x x) X0
       have i₂ := eq103917
       grind)
    | exact superpose eq103917 eq1710
    | exact resolve eq1710 eq103917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103917
  have eq167402 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq167318 X0
       have i₂ := eq1677 X0 (M.op (M.op x x) X0) x
       grind)
    | exact superpose eq1677 eq167318
    | exact resolve eq167318 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167318
  have eq167450 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op y (M.op x X0))) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq167402 X0
       have i₂ := eq2831 x X0
       grind)
    | exact superpose eq2831 eq167402
    | exact resolve eq167402 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831 eq167402
  have eq167496 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op X0 (M.op y (M.op y (M.op x X0))))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq75363 eq167450
    | exact resolve eq167450 eq75363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167450
  have eq167535 : x = (M.op (M.op (M.op x y) y) (M.op y (M.op y x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq167496 x
       have i₂ := eq99883 (M.op sF0 y) y x x
       grind)
    | exact superpose eq99883 eq167496
    | exact resolve eq167496 eq99883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99883 eq167496
  have eq167566 : x = (M.op (M.op (M.op x y) x) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq75363 eq167535
    | exact resolve eq167535 eq75363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75363 eq167535
  have eq168327 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) x) (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq167566 eq51284
    | exact resolve eq51284 eq167566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51284 eq167566
  have eq168360 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq168327
       have i₂ := eq3467 sF0 x y
       grind)
    | exact superpose eq3467 eq168327
    | exact resolve eq168327 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467 eq168327
  have eq168571 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq168360 eq101529
    | exact resolve eq101529 eq168360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101529 eq168360
  have eq168638 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq168571
  have eq168686 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq168638 eq39
    | exact resolve eq39 eq168638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq168638
  have eq168741 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq168686
    | exact resolve eq168686 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq168686
  have eq168742 : y = (M.op x y) ∨ x = y := by grind
  clear eq168741
  have eq168747 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq168742 eq20
    | exact resolve eq20 eq168742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168757 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq168742 eq1290
    | exact resolve eq1290 eq168742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290 eq168742
  have eq168777 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq168757 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq168757
    | (have j0 := eq168757 X0
       grind)
    | exact resolve eq168757 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168757
  have eq168778 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq168747
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq168747
    | exact resolve eq168747 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168747
  have eq168780 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq168778 eq26
    | exact resolve eq26 eq168778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168778
  have eq168903 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq168780 eq1815
    | exact resolve eq1815 eq168780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq168780
  have eq168961 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2165 eq168903
    | exact resolve eq168903 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168903
  have eq169906 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op (M.op x y) y))) ∨ x = y := by
    first
    | exact superpose eq168777 eq50878
    | exact resolve eq50878 eq168777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50878
  have eq169921 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op x y)) (M.op X0 y)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq168777 eq409
    | exact resolve eq409 eq168777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169929 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op x y)) X0) (M.op X0 y)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq168777 eq1710
    | exact resolve eq1710 eq168777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710 eq168777
  have eq170115 : ∀ X1 : G, (M.op (M.op (M.op X1 x) (M.op x y)) (M.op x y)) = X1 ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq169929 x x
       have i₂ := eq13654 x sF0 x
       grind)
    | exact superpose eq13654 eq169929
    | exact resolve eq169929 eq13654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13654 eq169929
  have eq170123 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) x) (M.op y (M.op X0 y))) = X1 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq17981 eq169921
    | exact resolve eq169921 eq17981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17981 eq169921
  have eq170129 : (M.op (σ x) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x (M.op y y)))) ∨ x = y := by
    first
    | exact superpose eq1654 eq169906
    | exact resolve eq169906 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq169906
  have eq170188 : ∀ X1 : G, (M.op (M.op (M.op X1 x) x) x) = X1 ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq170115 x
       have i₂ := eq7499 x x sF0
       grind)
    | exact superpose eq7499 eq170115
    | exact resolve eq170115 eq7499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170115
  have eq170196 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) x) X0) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq170123 X0 X1
       have i₂ := eq525 (M.op (M.op X1 X0) x) y X0
       grind)
    | exact superpose eq525 eq170123
    | exact resolve eq170123 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq170123
  have eq170202 : (σ (M.op x x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq170129
       have i₂ := eq1677 x x y
       grind)
    | exact superpose eq1677 eq170129
    | exact resolve eq170129 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170129
  have eq170254 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq170202
       have i₂ := eq135 x
       grind)
    | exact superpose eq135 eq170202
    | exact resolve eq170202 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170202
  have eq170296 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq170254
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq170254
    | exact resolve eq170254 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170254
  have eq182695 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) x)))) x) x) ∨ x = y := by
    first
    | exact superpose eq39434 eq170188
    | exact resolve eq170188 eq39434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39434 eq170188
  have eq182869 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) x) x) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) x)))) ∨ x = y := by
    first
    | (have i₁ := eq182695
       have i₂ := eq7499 sF1 (M.op sF1 (M.op sF2 (M.op sF3 x))) x
       grind)
    | exact superpose eq7499 eq182695
    | exact resolve eq182695 eq7499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7499 eq182695
  have eq182921 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (σ y) x)))) ∨ x = y := by
    first
    | exact superpose eq67348 eq182869
    | exact resolve eq182869 eq67348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67348 eq182869
  have eq182950 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq69155 eq182921
    | exact resolve eq182921 eq69155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69155 eq182921
  have eq182961 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ y))) ∨ x = y := by
    first
    | exact superpose eq2165 eq182950
    | exact resolve eq182950 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165 eq182950
  have eq182985 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ (M.op x y)))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq168961 eq182961
    | exact resolve eq182961 eq168961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168961 eq182961
  have eq183047 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ (M.op x y)))) ∨ x = y := by grind
  clear eq182985
  have eq192561 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) x) (M.op (σ x) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq170296 eq170196
    | exact resolve eq170196 eq170296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170196 eq170296
  have eq192564 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) x) (M.op (σ x) (σ x))) ∨ x = y := by grind
  clear eq192561
  have eq192575 : (σ x) = (M.op (M.op (M.op (σ x) x) x) (M.op x (σ x))) ∨ x = y := by
    first
    | exact superpose eq13470 eq192564
    | exact resolve eq192564 eq13470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13470 eq192564
  have eq192627 : (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op x x)))) (M.op x (σ x))) ∨ x = y := by
    first
    | exact superpose eq39637 eq192575
    | exact resolve eq192575 eq39637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39637 eq192575
  have eq192676 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (M.op (σ x) (M.op x x)) (M.op (σ (M.op x y)) (M.op x (σ x)))))) ∨ x = y := by
    first
    | (have i₁ := eq192627
       have i₂ := eq64805 sF1 (M.op sF2 (M.op x x)) sF1 (M.op x sF2)
       grind)
    | exact superpose eq64805 eq192627
    | exact resolve eq192627 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64805 eq192627
  have eq192720 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (M.op (σ (M.op x y)) (M.op x (σ x))) (M.op (σ x) (M.op x x))))) ∨ x = y := by
    first
    | (have i₁ := eq192676
       have i₂ := eq145001 sF1 x (M.op sF2 (M.op x x)) (M.op sF1 (M.op x sF2))
       grind)
    | (have i₁ := eq192676
       have i₂ := eq145001 sF1 x (M.op sF1 (M.op x sF2)) (M.op sF2 (M.op x x))
       grind)
    | exact superpose eq145001 eq192676
    | exact resolve eq192676 eq145001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145001 eq192676
  have eq192754 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op (M.op (σ (M.op x y)) (M.op x (σ x))) (M.op x (σ x)))) ∨ x = y := by
    first
    | (have i₁ := eq192720
       have i₂ := eq144909 x sF2 sF1 x (M.op sF1 (M.op x sF2))
       grind)
    | exact superpose eq144909 eq192720
    | exact resolve eq192720 eq144909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192720
  have eq192781 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op x (M.op (σ x) (M.op x (M.op (σ (M.op x y)) (M.op x (σ x)))))))) ∨ x = y := by
    first
    | (have i₁ := eq192754
       have i₂ := eq66670 (M.op sF1 (M.op x sF2)) x sF1 sF2
       grind)
    | exact superpose eq66670 eq192754
    | exact resolve eq192754 eq66670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66670 eq192754
  have eq192800 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op (σ x) (M.op x (M.op (σ (M.op x y)) (M.op x (σ x)))))) ∨ x = y := by
    first
    | (have i₁ := eq192781
       have i₂ := eq1822 sF1 x (M.op sF2 (M.op x (M.op sF1 (M.op x sF2)))) x
       grind)
    | exact superpose eq1822 eq192781
    | exact resolve eq192781 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822 eq192781
  have eq192817 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (σ x) (M.op (σ (M.op x y)) (M.op x (σ x)))))) ∨ x = y := by
    first
    | (have i₁ := eq192800
       have i₂ := eq3372 sF2 (M.op sF1 (M.op x sF2)) (M.op sF1 x) x
       grind)
    | (have i₁ := eq192800
       have i₂ := eq3372 x (M.op sF1 (M.op x sF2)) (M.op sF1 x) sF2
       grind)
    | exact superpose eq3372 eq192800
    | exact resolve eq192800 eq3372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372 eq192800
  have eq192833 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (σ (M.op x y)) (M.op (σ x) (M.op x (σ x)))))) ∨ x = y := by
    first
    | (have i₁ := eq192817
       have i₂ := eq144516 sF2 sF1 (M.op x sF2) sF1 x
       grind)
    | (have i₁ := eq192817
       have i₂ := eq144516 sF1 sF2 (M.op x sF2) sF1 x
       grind)
    | exact superpose eq144516 eq192817
    | exact resolve eq192817 eq144516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144516 eq192817
  have eq192847 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (M.op (σ (M.op x y)) (M.op (σ x) (σ x)))) ∨ x = y := by
    first
    | (have i₁ := eq192833
       have i₂ := eq144909 sF2 sF2 sF1 x sF1
       grind)
    | exact superpose eq144909 eq192833
    | exact resolve eq192833 eq144909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144909 eq192833
  have eq192861 : (σ x) = (M.op (M.op (σ (M.op x y)) x) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq192847
       have i₂ := eq1677 sF1 (M.op sF1 x) sF2
       grind)
    | exact superpose eq1677 eq192847
    | exact resolve eq192847 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677 eq192847
  have eq193308 : (σ (M.op x y)) = (M.op (σ x) (M.op x (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq192861 eq409
    | exact resolve eq409 eq192861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq192861
  have eq193895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq193308 eq183047
    | exact resolve eq183047 eq193308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183047 eq193308
  have eq193962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq193895
  have eq194013 : x = y := by
    first
    | (have r₁ := eq193962
       have r₂ := eq27
       grind)
    | exact resolve eq193962 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193962
  have eq194059 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq194013
       grind)
    | exact superpose eq194013 eq18
    | exact resolve eq18 eq194013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq194060 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq194013
       grind)
    | exact superpose eq194013 eq24
    | exact resolve eq24 eq194013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq194013
  have eq201932 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq194060
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq194060
    | exact resolve eq194060 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194060
  have eq203510 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq201932 eq26
    | exact resolve eq26 eq201932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq201932
  have eq210610 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq135 x
       have i₂ := eq194059
       grind)
    | exact superpose eq194059 eq135
    | exact resolve eq135 eq194059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq194059
  have eq210767 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq210610
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq210610
    | exact resolve eq210610 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq210610
  have eq210811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq203510 eq210767
    | exact resolve eq210767 eq203510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203510 eq210767
  have eq210840 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq210811
    | exact resolve eq210811 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq210811
  have eq210856 : False := by grind
  exact eq210856

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pxy_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
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
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq78 (σ X0)
       grind)
    | exact superpose eq78 eq10
    | exact resolve eq10 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq44
    | exact resolve eq44 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq82 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq78 sF2
       grind)
    | exact superpose eq78 eq50
    | exact resolve eq50 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq83 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq82
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq82
    | exact resolve eq82 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq84 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq78 sF2
       grind)
    | exact superpose eq78 eq81
    | exact resolve eq81 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq80
    | exact resolve eq80 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq92 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq78 sF3
       grind)
    | exact superpose eq78 eq76
    | exact resolve eq76 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq93 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq78 y
       grind)
    | exact superpose eq78 eq92
    | exact resolve eq92 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq78 sF1
       grind)
    | exact superpose eq78 eq136
    | exact resolve eq136 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq141 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq78 sF0
       grind)
    | exact superpose eq78 eq139
    | exact resolve eq139 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq139
  have eq162 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq141 eq16
    | exact resolve eq16 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq232 : x = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) X2 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) X1) (M.op (M.op X1 X2) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (M.op (M.op X1 X2) (M.op (σ X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (σ X0) (σ X0) X2
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq56
    | exact resolve eq56 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq648 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 X3 X2 x
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq56 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1129 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq55 eq549
    | exact resolve eq549 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1427 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq652
    | (have j0 := eq652 X0 (σ x) (σ y)
       grind)
    | exact resolve eq652 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1474 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op x y)
       have i₂ := eq652 sF0 x y
       grind)
    | exact superpose eq652 eq51
    | exact resolve eq51 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2209 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1427 (M.op (M.op X0 sF4) sF3)
       have i₂ := eq549 X0 sF4 sF3
       grind)
    | exact superpose eq549 eq1427
    | exact resolve eq1427 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2234 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq1427 eq14
    | exact resolve eq14 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2256 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1427 eq52
    | exact resolve eq52 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq2398 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2256 eq549
    | exact resolve eq549 eq2256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2476 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (σ y)))) := by
    first
    | exact superpose eq241 eq243
    | exact resolve eq243 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq243
  have eq2552 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq52 eq2476
    | exact resolve eq2476 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2476
  have eq2559 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1129 eq2552
    | exact resolve eq2552 eq1129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq3708 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq2209 eq549
    | exact resolve eq549 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq2209
  have eq7223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq7223
    | exact resolve eq7223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7223
  have eq7227 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq7224
       have r₂ := eq28
       grind)
    | exact resolve eq7224 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7224
  have eq7229 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq7227
    | exact resolve eq7227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7227
  have eq7234 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7229 eq67
    | (have r₁ := eq67
       have r₂ := eq7229
       grind)
    | exact resolve eq67 eq7229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq7246 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7229 eq1129
    | exact resolve eq1129 eq7229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq7256 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7229 eq2256
    | exact resolve eq2256 eq7229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256 eq7229
  have eq7267 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq7234
  have eq7275 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3708 eq7246
    | exact resolve eq7246 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3708 eq7246
  have eq7720 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7267 eq109
    | exact resolve eq109 eq7267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq7267
  have eq7724 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7720
  have eq7839 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7724 eq7256
    | exact resolve eq7256 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7256
  have eq7845 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7724 eq551
    | exact resolve eq551 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq7724
  have eq7871 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq7839
  have eq7884 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7871 eq2234
    | exact resolve eq2234 eq7871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234 eq7871
  have eq8118 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7275 eq2398
    | (have j1 := eq7275 (σ x)
       grind)
    | exact resolve eq2398 eq7275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398
  have eq8150 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq8118
    | exact resolve eq8118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8118
  have eq17403 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7884 eq7275
    | exact resolve eq7275 eq7884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7275
  have eq17447 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq17403
  have eq17457 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2559 eq17447
    | exact resolve eq17447 eq2559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559 eq17447
  have eq18067 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17457 eq7845
    | exact resolve eq7845 eq17457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7845 eq17457
  have eq18123 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18067
  have eq18767 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18123 eq162
    | exact resolve eq162 eq18123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq18123
  have eq18819 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq18767
    | exact resolve eq18767 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18767
  have eq20057 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18819 eq232
    | exact resolve eq232 eq18819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq18819
  have eq20151 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq20057
       grind)
    | exact superpose eq20057 eq84
    | exact resolve eq84 eq20057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq20057
  have eq20246 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20151
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20151
    | exact resolve eq20151 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20151
  have eq23970 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20246 eq7884
    | exact resolve eq7884 eq20246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7884 eq20246
  have eq24044 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq23970
  have eq24692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24044 eq8150
    | exact resolve eq8150 eq24044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8150 eq24044
  have eq24764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq24692
  have eq24783 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq24764
       have r₂ := eq28
       grind)
    | exact resolve eq24764 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24764
  have eq24795 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24783 eq30
    | exact resolve eq30 eq24783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq24783
  have eq24862 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq24795
    | exact resolve eq24795 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq24795
  have eq24863 : y = (M.op x y) ∨ x = y := by grind
  clear eq24862
  have eq24866 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24863 eq21
    | exact resolve eq21 eq24863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24908 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op X0 y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq24863 eq1474
    | exact resolve eq1474 eq24863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474 eq24863
  have eq24951 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24866
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24866
    | exact resolve eq24866 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24866
  have eq49906 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op (M.op (σ x) X0) (M.op (M.op X0 X1) (M.op (σ (M.op y y)) X1))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq601 (M.op y y) X0 X1
       have i₂ := eq24908 y
       grind)
    | exact superpose eq24908 eq601
    | exact resolve eq601 eq24908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq24908
  have eq50043 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op (M.op X0 X1) (M.op (M.op (σ y) (σ y)) X1))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq49906 X0 X1
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq49906
    | exact resolve eq49906 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq49906
  have eq50089 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op (M.op X0 X1) (M.op (M.op (σ y) (σ y)) X1))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq50043 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq50043
    | (have j0 := eq50043 X0 X1
       grind)
    | exact resolve eq50043 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50043
  have eq50099 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y))) ∨ x = y := by
    first
    | exact superpose eq595 eq50089
    | exact resolve eq50089 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq50089
  have eq50101 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq50099
       have i₂ := eq652 sF4 sF3 sF3
       grind)
    | exact superpose eq652 eq50099
    | exact resolve eq50099 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq50099
  have eq50225 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op (M.op X0 (M.op X1 (σ y))) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq50101 eq648
    | exact resolve eq648 eq50101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50101
  have eq50243 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq50225 x x
       have i₂ := eq648 x x sF3 sF3
       grind)
    | exact superpose eq648 eq50225
    | exact resolve eq50225 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq50225
  have eq50307 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq50243 eq28
    | exact resolve eq28 eq50243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50243
  have eq50405 : x = y := by
    first
    | (have r₁ := eq50307
       have r₂ := eq24951
       grind)
    | exact resolve eq50307 eq24951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24951 eq50307
  have eq50407 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq50405
       grind)
    | exact superpose eq50405 eq19
    | exact resolve eq19 eq50405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq50408 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq50405
       grind)
    | exact superpose eq50405 eq25
    | exact resolve eq25 eq50405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq50405
  have eq50484 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq50408
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq50408
    | exact resolve eq50408 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq50408
  have eq50491 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50484 eq27
    | exact resolve eq27 eq50484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq50484
  have eq50826 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq50491 eq83
    | exact resolve eq83 eq50491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq50491
  have eq51016 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq50826
       have i₂ := eq50407
       grind)
    | exact superpose eq50407 eq50826
    | exact resolve eq50826 eq50407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50407 eq50826
  have eq51348 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51016 eq15
    | exact resolve eq15 eq51016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51016
  have eq51390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq51348
    | exact resolve eq51348 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq51348
  have eq51399 : False := by grind
  exact eq51399

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_pyy_pxy_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
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
  have eq56 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = (k X0 (M.op (M.op X1 X2) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op X1 X2) (M.op X0 X2))
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have r₂ := eq9 X0 X1 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X2 X3)) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq30 (M.op X1 X2) X3 X2 x
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq30 X0 x X2 X1
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq84 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X1 X2) (M.op X0 X2) X0
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X1 X0) X2 (M.op X0 X2)
       have i₂ := eq70 X1 X0 X2
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 (M.op X0 X1) X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq84
    | exact resolve eq84 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq126 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126
    | (have j0 := eq126 (σ X0) (σ X1)
       grind)
    | exact resolve eq126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq72 X1 X0 X0
       grind)
    | exact superpose eq72 eq133
    | exact resolve eq133 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq133
  have eq301 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X2
       have i₂ := eq231 X1 X2 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq231 eq9
    | exact resolve eq9 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq451 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq428 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq843 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq451 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq1678 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 x y
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 x y
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq1749 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq843 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq2122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2111 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2111
    | exact resolve eq2111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2125 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2122 X0
       have i₂ := eq2111 X0
       grind)
    | exact superpose eq2111 eq2122
    | exact resolve eq2122 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq2122
  have eq2214 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231 (σ X0) X2 X1
       have i₂ := eq2125 X0
       grind)
    | exact superpose eq2125 eq231
    | exact resolve eq231 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq5106 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1678
       have i₂ := eq2125 x
       grind)
    | exact superpose eq2125 eq1678
    | exact resolve eq1678 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq5110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5106
       have i₂ := eq126 x y
       grind)
    | exact superpose eq126 eq5106
    | (have j1 := eq126 x y
       grind)
    | exact resolve eq5106 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq5106
  have eq5111 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq5110
  have eq5120 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5111
       grind)
    | exact superpose eq5111 eq10
    | exact resolve eq10 eq5111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5147 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5120
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5120
    | exact resolve eq5120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5120
  have eq5148 : y = (M.op x x) := by grind
  clear eq5147
  have eq5169 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2214 x X1 X0
       have i₂ := eq5148
       grind)
    | exact superpose eq5148 eq2214
    | exact resolve eq2214 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq5180 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq70 x x X0
       have i₂ := eq5148
       grind)
    | exact superpose eq5148 eq70
    | exact resolve eq70 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5181 : ∀ X0 : G, (M.op (M.op (M.op X0 x) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 X0 x x
       have i₂ := eq5148
       grind)
    | exact superpose eq5148 eq70
    | exact resolve eq70 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq5148
  have eq5264 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op (M.op x X0) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (M.op y X0) X1 (M.op x X0)
       have i₂ := eq5180 X0
       grind)
    | exact superpose eq5180 eq85
    | exact resolve eq85 eq5180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq5180
  have eq5284 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5264 X0 X1
       have i₂ := eq84 x X1 X0
       grind)
    | exact superpose eq84 eq5264
    | exact resolve eq5264 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq5264
  have eq5601 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq5181 (M.op X0 (M.op X1 X1))
       have i₂ := eq301 X0 X1 x
       grind)
    | exact superpose eq301 eq5181
    | exact resolve eq5181 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq5181
  have eq11026 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1749 X0 X1
       have i₂ := eq5601 X0 (M.op X0 X1)
       grind)
    | exact superpose eq5601 eq1749
    | exact resolve eq1749 eq5601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749 eq5601
  have eq11075 : ∀ X0 : G, (M.op (σ X0) y) = (k (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11026 (σ X0) (σ X0)
       have i₂ := eq2125 X0
       grind)
    | exact superpose eq2125 eq11026
    | exact resolve eq11026 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11129 : ∀ X0 : G, (M.op (σ X0) y) = (k (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11075 X0
       have i₂ := eq2125 (M.op X0 X0)
       grind)
    | exact superpose eq2125 eq11075
    | exact resolve eq11075 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125 eq11075
  have eq11143 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11129 X0
       have i₂ := eq15 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq15 eq11129
    | exact resolve eq11129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11129
  have eq11146 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq11143 X0
       have i₂ := eq11026 X0 X0
       grind)
    | exact superpose eq11026 eq11143
    | exact resolve eq11143 eq11026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11026 eq11143
  have eq14226 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq5169 y X0
       have i₂ := eq5284 (σ y) X0
       grind)
    | exact superpose eq5284 eq5169
    | exact resolve eq5169 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5169 eq5284
  have eq14499 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14226 (σ x)
       grind)
    | exact superpose eq14226 eq16
    | exact resolve eq16 eq14226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14226
  have eq14519 : False := by grind
  exact eq14519

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyy_x_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq32 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq28
    | (have j0 := eq28 (M.op x y)
       grind)
    | exact resolve eq28 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq35 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq24
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
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
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq83 : ∀ X0 : G, (M.op (M.op (M.op X0 x) x) (M.op (M.op x y) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq9 X0 X1 y
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq91 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ y) X1)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) (M.op sF3 X1))
       have i₂ := eq9 X0 X1 sF3
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
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
  clear eq56
  have eq96 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq93 eq9
    | exact resolve eq9 eq93
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
  have eq104 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (M.op X1 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : x ≠ (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq116 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq60 eq116
    | exact resolve eq116 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq126 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60 eq126
    | exact resolve eq126 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq141 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq180 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
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
  clear eq141
  have eq314 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq326 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq337 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq326
    | exact resolve eq326 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq339 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq337
    | exact resolve eq337 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq341 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq339
    | exact resolve eq339 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq353 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq78 eq83
    | exact resolve eq83 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq93 eq96
    | exact resolve eq96 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op x x) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x x)) := by
    first
    | exact superpose eq353 eq13
    | (have j0 := eq13 (M.op (M.op x y) (M.op x y)) (M.op x x)
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) (M.op x y)) (M.op x x)
       have r₂ := eq353
       grind)
    | exact resolve eq13 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : (M.op (M.op x y) (M.op x y)) ≠ (M.op x x) ∨ (k (M.op (M.op x y) (M.op x y)) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq353 eq12
    | (have j0 := eq12 (M.op (M.op x y) (M.op x y)) (M.op x x)
       grind)
    | exact resolve eq12 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : (M.op (M.op x y) (M.op x y)) = (M.op x x) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x x)) := by grind
  clear eq428
  have eq451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq341
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq341
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq341 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq451
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq451
    | exact resolve eq451 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq461
    | exact resolve eq461 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq463 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq462
       have r₂ := eq27
       grind)
    | exact resolve eq462 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq464 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq463
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq463
    | exact resolve eq463 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq465 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq464
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq464
    | exact resolve eq464 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq466 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq465 eq27
    | exact resolve eq27 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq465 eq129
    | (have r₁ := eq129
       have r₂ := eq465
       grind)
    | exact resolve eq129 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq465
  have eq480 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq477
  have eq481 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq480
       have r₂ := eq479
       grind)
    | exact resolve eq480 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq480
  have eq484 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq481
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq481
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq481 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq481
       grind)
    | exact superpose eq481 eq10
    | exact resolve eq10 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq506 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39 eq487
    | exact resolve eq487 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq507 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq484
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq484
    | exact resolve eq484 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq508 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq506
       have r₂ := eq118
       grind)
    | exact resolve eq506 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq509 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq507
    | exact resolve eq507 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq510 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq509
       have r₂ := eq466
       grind)
    | exact resolve eq509 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq509
  have eq511 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq510
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq510
    | exact resolve eq510 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq512 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq511
  have eq513 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq512
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq512
    | exact resolve eq512 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq514 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq513
  have eq515 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) (M.op X5 X4)) X5) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X4 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X2 X3) X4 X5
       have i₂ := eq53 X0 X3 X2 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X5 (M.op X0 X4))) X5) = (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) := by
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
  have eq534 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X4 X2)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53 X0 x X2 X4
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (σ y))) X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq395 eq53
    | exact resolve eq53 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 X3) (M.op X2 X3)) := by
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
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
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
  have eq578 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
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
  have eq579 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
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
  have eq580 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
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
  have eq586 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x y) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op y X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 (M.op y X2))
       have i₂ := eq53 X0 X1 X2 y
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op (σ y) X2))) := by
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
  have eq606 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X4) (M.op (M.op X4 X5) (M.op (M.op X2 X3) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op X0 X3) (M.op X2 X3) X5
       have i₂ := eq53 X0 X3 X2 X1
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op (M.op X4 X5) (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X5))) := by
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
  have eq610 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) X1) (M.op (M.op X1 X2) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq55
    | exact resolve eq55 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) (M.op (M.op X4 X5) (M.op X3 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op X0 (M.op X3 X2)) X3 X5
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) (M.op (M.op (M.op x y) (M.op x y)) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq83 eq55
    | exact resolve eq55 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) (M.op (M.op X2 X1) X3))) := by
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
  have eq693 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
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
  have eq694 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op (M.op X1 X4) X3)) := by
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
  have eq699 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X5 X4)) X5) := by
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
  have eq700 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X5 (M.op (M.op X0 X4) X2))) X5) := by
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
  have eq728 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op X0 (σ y))) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq514 eq57
    | exact resolve eq57 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq514 eq93
    | exact resolve eq93 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq736 : (σ x) ≠ (σ x) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq514 eq117
    | (have r₁ := eq117
       have r₂ := eq514
       grind)
    | exact resolve eq117 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq736
  have eq742 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104 eq728
    | exact resolve eq728 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq728
  have eq745 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq341
       have i₂ := eq508
       grind)
    | exact superpose eq508 eq341
    | exact resolve eq341 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq745
  have eq753 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq749
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq749
    | exact resolve eq749 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq754 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq753
  have eq756 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq754 eq27
    | exact resolve eq27 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq807 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730 eq96
    | exact resolve eq96 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq395 eq807
    | exact resolve eq807 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq827 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq742 eq101
    | exact resolve eq101 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq920 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) X1))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq821 eq55
    | exact resolve eq55 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq933 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq827 eq96
    | exact resolve eq96 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq952 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq395 eq933
    | exact resolve eq933 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq1527 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq739
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq739
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq739 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1536 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq739
       grind)
    | exact superpose eq739 eq10
    | exact resolve eq10 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq1552 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1527
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1527
    | exact resolve eq1527 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq1555 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1552
    | exact resolve eq1552 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1558 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1555
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1555
    | exact resolve eq1555 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1559 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1558
  have eq1562 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1559
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1559
    | exact resolve eq1559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq1563 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1562
  have eq1577 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1563 eq730
    | exact resolve eq730 eq1563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq1563
  have eq1590 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1577
  have eq1595 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1590 eq96
    | exact resolve eq96 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1612 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq395 eq1595
    | exact resolve eq1595 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1641 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1612 eq395
    | exact resolve eq395 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq1647 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1612 eq952
    | exact resolve eq952 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1658 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1647
  have eq1948 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq573 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) X2 X3
       have i₂ := eq573 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq573 eq573
    | exact resolve eq573 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1952 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (σ y))) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq57 eq573
    | exact resolve eq573 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1953 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X3 X4) X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq573 (M.op X0 (M.op (M.op X3 X4) X2)) X3 X4
       have i₂ := eq53 X0 X1 X2 (M.op X3 X4)
       grind)
    | exact superpose eq53 eq573
    | exact resolve eq573 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1960 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq96 eq573
    | exact resolve eq573 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1979 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (M.op X0 (M.op X1 X2)) X1 X3
       have i₂ := eq573 X0 X1 X2
       grind)
    | exact superpose eq573 eq55
    | exact resolve eq55 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1983 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2
       have i₂ := eq573 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq573 eq9
    | exact resolve eq9 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1984 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq83 (M.op X0 (M.op x x))
       have i₂ := eq573 X0 x x
       grind)
    | exact superpose eq573 eq83
    | exact resolve eq83 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2086 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq1984 eq353
    | exact resolve eq353 eq1984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq1984
  have eq2107 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq920 x x
       have i₂ := eq1979 (M.op (M.op sF2 sF2) x) sF4 x x
       grind)
    | exact superpose eq1979 eq920
    | exact resolve eq920 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq2147 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1960 eq568
    | exact resolve eq568 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq1960
  have eq2161 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ (M.op x y))) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1952 eq1641
    | exact resolve eq1641 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq2167 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) = (M.op (M.op X3 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq528 X0 X1 X2 X3 X4 x
       have i₂ := eq1948 X3 x X0 X4
       grind)
    | exact superpose eq1948 eq528
    | exact resolve eq528 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq2168 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X0 X4)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq700 X0 X1 X2 X3 X4 x
       have i₂ := eq1948 X1 x (M.op X0 X4) X2
       grind)
    | exact superpose eq1948 eq700
    | exact resolve eq700 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq2225 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x x)) ∨ (M.op (M.op x y) (M.op x y)) ≠ (M.op x x) := by
    first
    | (have i₁ := eq429
       have i₂ := eq2086
       grind)
    | exact superpose eq2086 eq429
    | exact resolve eq429 eq2086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq2086
  have eq2248 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2147 eq2107
    | exact resolve eq2107 eq2147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107 eq2147
  have eq2250 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1952 eq2161
    | exact resolve eq2161 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952 eq2161
  have eq2288 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x x)) := by
    first
    | (have r₁ := eq2225
       have r₂ := eq432
       grind)
    | exact resolve eq2225 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq2225
  have eq2296 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2250
       have i₂ := eq693 sF4 sF1 sF3
       grind)
    | exact superpose eq693 eq2250
    | exact resolve eq2250 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250
  have eq2421 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (M.op (σ x) X0))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2248 eq55
    | exact resolve eq55 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248
  have eq2443 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2421 x
       have i₂ := eq1979 sF4 sF2 sF2 x
       grind)
    | exact superpose eq1979 eq2421
    | exact resolve eq2421 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq2494 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ x)) X1))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2443 eq55
    | exact resolve eq55 eq2443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq2443
  have eq2635 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq514 eq2296
    | exact resolve eq2296 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq2296
  have eq2656 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2635
  have eq2668 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq580
    | exact resolve eq580 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2669 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq580 (M.op X0 (M.op X3 X2)) X3 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq580
    | exact resolve eq580 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2815 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X4 X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3 X4
       have i₂ := eq580 X0 X1 X2
       grind)
    | exact superpose eq580 eq53
    | exact resolve eq53 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2835 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op X0 (M.op X4 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq699 X0 X1 X2 X3 X4 x
       have i₂ := eq2815 X0 X1 X2 X4 x
       grind)
    | exact superpose eq2815 eq699
    | exact resolve eq699 eq2815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq2815
  have eq2925 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op x (M.op y X1))) := by
    intro X0 X1
    first
    | exact superpose eq578 eq693
    | exact resolve eq693 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq2926 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq579 eq693
    | exact resolve eq693 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2930 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq693 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq580 X0 X2 X3
       grind)
    | exact superpose eq580 eq693
    | exact resolve eq693 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2931 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X3 X2))) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq693 X1 (M.op (M.op X0 X2) (M.op X3 X2)) X3
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq693
    | exact resolve eq693 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2935 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op X0 (M.op x (M.op (M.op x y) (M.op y y)))) := by
    intro X0
    first
    | exact superpose eq80 eq693
    | exact resolve eq693 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2939 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | exact superpose eq101 eq693
    | exact resolve eq693 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2981 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq693 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq573 X0 X2 X2
       grind)
    | exact superpose eq573 eq693
    | exact resolve eq693 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3009 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op X2 X1)
       have i₂ := eq693 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq693 eq9
    | exact resolve eq9 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3020 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op x y)
       have i₂ := eq693 sF0 x y
       grind)
    | exact superpose eq693 eq52
    | exact resolve eq52 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3023 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq57 (M.op x sF3)
       have i₂ := eq693 sF4 x sF3
       grind)
    | exact superpose eq693 eq57
    | exact resolve eq57 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq693
  have eq3075 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq2981 sF0 (M.op sF0 x) y
       grind)
    | exact superpose eq2981 eq80
    | exact resolve eq80 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3084 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq2981 sF4 (M.op sF4 sF2) sF3
       grind)
    | exact superpose eq2981 eq101
    | exact resolve eq101 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq3133 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2939 X0
       have i₂ := eq2981 sF4 sF2 sF3
       grind)
    | exact superpose eq2981 eq2939
    | exact resolve eq2939 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq3141 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2935 X0
       have i₂ := eq2981 sF0 x y
       grind)
    | exact superpose eq2981 eq2935
    | exact resolve eq2935 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935
  have eq3287 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1979 X0 X1 X2 x
       have i₂ := eq2931 X2 X0 x X1
       grind)
    | exact superpose eq2931 eq1979
    | exact resolve eq1979 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq3288 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 (M.op X0 X4)) X2) = (M.op (M.op X1 (M.op X2 X4)) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2168 X2 X1 X0 x X4
       have i₂ := eq2931 X0 X1 x X4
       grind)
    | exact superpose eq2931 eq2168
    | exact resolve eq2168 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq3291 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2835 X0 X2 X1 x X4
       have i₂ := eq2931 X1 X4 x X2
       grind)
    | exact superpose eq2931 eq2835
    | exact resolve eq2835 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835
  have eq3292 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq629 X0 X1 X2 x
       have i₂ := eq2931 X2 X0 x (M.op X2 X1)
       grind)
    | exact superpose eq2931 eq629
    | exact resolve eq629 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq3299 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq607 X0 X1 X2 X3 X4 x
       have i₂ := eq2931 X4 (M.op X0 X4) x (M.op (M.op X2 X3) (M.op X1 X3))
       grind)
    | exact superpose eq2931 eq607
    | exact resolve eq607 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq3300 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op X1 (M.op (M.op x y) (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq614 X0 X0 x
       have i₂ := eq2931 X0 (M.op X0 X0) x (M.op sF0 sF0)
       grind)
    | exact superpose eq2931 eq614
    | exact resolve eq614 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq3308 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X4) (M.op X4 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq606 X0 X1 X2 X3 X4 x
       have i₂ := eq2931 X4 (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X4) x (M.op X2 X3)
       grind)
    | exact superpose eq2931 eq606
    | exact resolve eq606 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq3309 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq611 X0 X1 X2 X3 X4 x
       have i₂ := eq2931 X4 (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) x X3
       grind)
    | exact superpose eq2931 eq611
    | exact resolve eq611 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq3314 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq610 x X0 x
       have i₂ := eq2931 X0 (M.op sF2 X0) x x
       grind)
    | exact superpose eq2931 eq610
    | exact resolve eq610 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq3317 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op (σ x) (σ x)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2494 X0 x
       have i₂ := eq2931 X0 (M.op sF4 X0) x (M.op sF2 sF2)
       grind)
    | exact superpose eq2931 eq2494
    | exact resolve eq2494 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2494
  have eq3321 : ∀ X0 X2 : G, x = (M.op (M.op (M.op x y) (M.op X0 X2)) (M.op X0 (M.op y X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq586 X0 X2 x
       have i₂ := eq2931 X0 sF0 X2 x
       grind)
    | exact superpose eq2931 eq586
    | exact resolve eq586 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq3322 : ∀ X0 X2 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) (M.op X0 (M.op (σ y) X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq588 X0 X2 x
       have i₂ := eq2931 X0 sF4 X2 x
       grind)
    | exact superpose eq2931 eq588
    | exact resolve eq588 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq2931
  have eq3326 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) X4) = (M.op X0 (M.op X3 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1953 X0 X1 X2 X3 X4
       have i₂ := eq2930 X3 X0 X4 X2
       grind)
    | exact superpose eq2930 eq1953
    | exact resolve eq1953 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq3372 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2167 X0 X1 X2 X3 X4
       have i₂ := eq2930 X0 (M.op X3 (M.op X2 X4)) (M.op X1 X2) X1
       grind)
    | exact superpose eq2930 eq2167
    | exact resolve eq2167 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq3422 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op X1 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq694 X0 X1 X2 X3 X4
       have i₂ := eq2930 X1 (M.op (M.op (M.op X0 X1) X2) X3) X4 X3
       grind)
    | exact superpose eq2930 eq694
    | exact resolve eq694 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq3441 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ y)))) X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq559 X0 X2 X2
       have i₂ := eq2930 X0 sF4 X2 sF3
       grind)
    | exact superpose eq2930 eq559
    | exact resolve eq559 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq3564 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) := by
    intro X0
    first
    | exact superpose eq2926 eq3133
    | exact resolve eq3133 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq3568 : ∀ X0 : G, (M.op X0 (M.op x (M.op x y))) = (M.op X0 (M.op x (M.op y x))) := by
    intro X0
    first
    | exact superpose eq2925 eq3141
    | exact resolve eq3141 eq2925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq3622 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3317 X0
       have i₂ := eq2981 X0 (M.op sF4 X0) sF2
       grind)
    | exact superpose eq2981 eq3317
    | exact resolve eq3317 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq3639 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3300 X0 X0
       have i₂ := eq2981 X0 (M.op X0 X0) sF0
       grind)
    | exact superpose eq2981 eq3300
    | exact resolve eq3300 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300
  have eq3640 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op X2 (M.op X3 (M.op X1 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3299 X0 X1 X2 X3 X4
       have i₂ := eq2930 X2 X4 X3 (M.op X1 X3)
       grind)
    | exact superpose eq2930 eq3299
    | exact resolve eq3299 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3299
  have eq3696 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2656
       have i₂ := eq3287 sF2 sF2 sF1
       grind)
    | (have i₁ := eq2656
       have i₂ := eq3287 sF2 sF1 sF2
       grind)
    | exact superpose eq3287 eq2656
    | exact resolve eq2656 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2656
  have eq3765 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3372 X0 X1 X2 X3 X4
       have i₂ := eq3291 (M.op X3 (M.op X2 X4)) (M.op X1 X2) X1 X0
       grind)
    | (have i₁ := eq3372 X0 X1 X2 X3 X4
       have i₂ := eq3291 (M.op X3 (M.op X2 X4)) X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq3291 eq3372
    | exact resolve eq3372 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372
  have eq3880 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3564 X0
       have i₂ := eq1983 X0 sF2 sF3
       grind)
    | exact superpose eq1983 eq3564
    | exact resolve eq3564 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564
  have eq3883 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3568 X0
       have i₂ := eq1983 X0 x y
       grind)
    | exact superpose eq1983 eq3568
    | exact resolve eq3568 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq3953 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq3640 X0 X1 X2 x X4
       have i₂ := eq1983 X2 x X1
       grind)
    | exact superpose eq1983 eq3640
    | exact resolve eq3640 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640
  have eq4030 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3765 X0 x X2 X3 X4
       have i₂ := eq3292 X0 X2 x
       grind)
    | exact superpose eq3292 eq3765
    | exact resolve eq3765 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3765
  have eq4756 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1612 eq3622
    | exact resolve eq3622 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq4787 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4756
  have eq4829 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4787 eq9
    | exact resolve eq9 eq4787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq5232 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3696 eq53
    | exact resolve eq53 eq3696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696
  have eq5253 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2668 eq5232
    | (have j0 := eq5232 (σ y)
       grind)
    | exact resolve eq5232 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668 eq5232
  have eq5255 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5253
    | exact resolve eq5253 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253
  have eq5977 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5255 eq821
    | exact resolve eq821 eq5255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq5980 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5255 eq1612
    | exact resolve eq1612 eq5255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq5255
  have eq6005 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5980
  have eq6008 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5977
  have eq6029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6005 eq12
    | (have r₁ := eq12 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq6005
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6005
       grind)
    | exact resolve eq12 eq6005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6037 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6029
  have eq6044 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq6037
    | exact resolve eq6037 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6037
  have eq6051 : (k (M.op x y) (M.op x y)) = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6044 eq10
    | exact resolve eq10 eq6044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6044
  have eq6071 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq6051
    | exact resolve eq6051 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6051
  have eq6077 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6071 eq14
    | (have j0 := eq14 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq14 eq6071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6071
  have eq6079 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6077
  have eq6085 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6079 eq78
    | exact resolve eq78 eq6079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq6131 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6085 eq3292
    | exact resolve eq3292 eq6085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6085
  have eq6134 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6131 X0
       have i₂ := eq3287 X0 sF0 x
       grind)
    | (have i₁ := eq6131 X0
       have i₂ := eq3287 X0 x sF0
       grind)
    | exact superpose eq3287 eq6131
    | exact resolve eq6131 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6131
  have eq6140 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3883 eq6134
    | exact resolve eq6134 eq3883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6134
  have eq7688 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) X1)) X2) (M.op (σ y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 (M.op (M.op X0 X1) (M.op sF4 X1)) X1
       have i₂ := eq9 X0 X1 sF4
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7798 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq7688 X0 x x
       have i₂ := eq2669 X0 x sF4 sF3 x
       grind)
    | exact superpose eq2669 eq7688
    | exact resolve eq7688 eq2669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2669 eq7688
  have eq9545 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6140 x
       grind)
    | exact superpose eq6140 eq18
    | (have j1 := eq6140 x
       grind)
    | exact resolve eq18 eq6140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6140
  have eq10330 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 (σ y))) (M.op (M.op (σ x) X0) (M.op X0 X1))) = (M.op (M.op X2 (M.op X3 (M.op (σ x) (σ y)))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3314 eq53
    | exact resolve eq53 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10361 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X2) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3314 eq580
    | exact resolve eq580 eq3314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314
  have eq10372 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10361 X2 X0 x
       have i₂ := eq2930 X0 (M.op (M.op sF4 (M.op X2 sF3)) x) X2 x
       grind)
    | exact superpose eq2930 eq10361
    | exact resolve eq10361 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10361
  have eq10400 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 (M.op (σ x) (σ y)))) X3) = (M.op (M.op X2 (M.op X1 (σ y))) (M.op (σ x) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10330 X2 X1 X2 X3
       have i₂ := eq2930 sF2 (M.op X2 (M.op X1 sF3)) X2 (M.op X2 X1)
       grind)
    | exact superpose eq2930 eq10330
    | exact resolve eq10330 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10330
  have eq10580 : ∀ X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 (M.op (σ x) (σ y)))) X3) = (M.op (M.op X2 (M.op X1 (σ y))) (M.op (σ x) X1)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq10400 X2 X1 X2 X3
       have i₂ := eq3292 sF2 X1 X2
       grind)
    | exact superpose eq3292 eq10400
    | exact resolve eq10400 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10400
  have eq10724 : ∀ X2 X3 : G, (M.op (M.op X2 (M.op X3 (M.op (σ x) (σ y)))) X3) = (M.op (M.op X2 (σ x)) (σ y)) := by
    intro X2 X3
    first
    | (have i₁ := eq10580 x X3 X3
       have i₂ := eq4030 (M.op x sF3) X2 X3 (M.op sF2 x)
       grind)
    | (have i₁ := eq10580 X2 X3 X3
       have i₂ := eq4030 sF2 X2 X3 sF3
       grind)
    | exact superpose eq4030 eq10580
    | exact resolve eq10580 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10580
  have eq10838 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10724 eq4829
    | exact resolve eq4829 eq10724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4829
  have eq11090 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x (M.op y x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3321 x x
       have i₂ := eq9545
       grind)
    | exact superpose eq9545 eq3321
    | exact resolve eq3321 eq9545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321 eq9545
  have eq11302 : x = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11090
       have i₂ := eq1983 (M.op sF0 sF0) x y
       grind)
    | exact superpose eq1983 eq11090
    | exact resolve eq11090 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11090
  have eq11993 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1658 eq10838
    | exact resolve eq10838 eq1658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658 eq10838
  have eq12025 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11993
  have eq12092 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12025 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq12025
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12025
       grind)
    | exact resolve eq12 eq12025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12025
  have eq12104 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12092
  have eq12119 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq12104
    | exact resolve eq12104 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq12104
  have eq12664 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) X0) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3322 eq573
    | exact resolve eq573 eq3322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq3322
  have eq15561 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6079 eq11302
    | exact resolve eq11302 eq6079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079 eq11302
  have eq15583 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15561
  have eq18803 : (k y x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6008 eq1536
    | exact resolve eq1536 eq6008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536 eq6008
  have eq18820 : (k y x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18803
  have eq19437 : (k y (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12119 eq10
    | exact resolve eq10 eq12119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12119
  have eq19502 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6005 eq19437
    | exact resolve eq19437 eq6005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6005
  have eq19507 : (k y (M.op x y)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19437 eq18820
    | exact resolve eq18820 eq19437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18820 eq19437
  have eq19524 : (k y (M.op x y)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19507
  have eq19529 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19502
  have eq19531 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq19529
    | exact resolve eq19529 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq19529
  have eq19815 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X1)) (M.op X0 X5)) = (M.op (M.op X3 (M.op X4 (M.op X2 X5))) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq534 X3 X4 (M.op X2 X5) (M.op X0 X5)
       have i₂ := eq53 X0 X5 X2 X1
       grind)
    | exact superpose eq53 eq534
    | exact resolve eq534 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq19999 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X0 (M.op X2 (M.op X3 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq534 X0 X2 (M.op X3 X1) X3
       have i₂ := eq3292 X0 X1 X3
       grind)
    | exact superpose eq3292 eq534
    | exact resolve eq534 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq20257 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq19999 X0 X3 x X1
       have i₂ := eq1948 X0 x X1 X3
       grind)
    | exact superpose eq1948 eq19999
    | exact resolve eq19999 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19999
  have eq20407 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X1)) (M.op X0 X5)) = (M.op (M.op X3 X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq19815 X0 X1 X2 X3 x X5
       have i₂ := eq1948 X3 x X2 X5
       grind)
    | exact superpose eq1948 eq19815
    | exact resolve eq19815 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq19815
  have eq20765 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) (M.op X5 X4)) X5) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X4 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq515 X0 X1 X2 X3 X4 X5
       have i₂ := eq20257 X0 X1 (M.op X1 X2)
       grind)
    | (have i₁ := eq515 X0 X1 X2 X3 X4 X5
       have i₂ := eq20257 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq20257 eq515
    | exact resolve eq515 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq20775 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X4) (M.op X4 (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3308 X0 X1 X2 X3 X4
       have i₂ := eq20257 X0 X1 (M.op X1 X2)
       grind)
    | (have i₁ := eq3308 X0 X1 X2 X3 X4
       have i₂ := eq20257 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq20257 eq3308
    | exact resolve eq3308 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq20835 : ∀ X2 X3 : G, (M.op (M.op X2 (σ x)) (σ y)) = (M.op (M.op X2 X3) (M.op X3 (M.op (σ x) (σ y)))) := by
    intro X2 X3
    first
    | (have i₁ := eq10724 x x
       have i₂ := eq20257 x x (M.op x sF4)
       grind)
    | (have i₁ := eq10724 x X3
       have i₂ := eq20257 x (M.op X3 sF4) X3
       grind)
    | exact superpose eq20257 eq10724
    | exact resolve eq10724 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10724
  have eq20888 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq20257 X0 x sF0
       grind)
    | (have i₁ := eq87 X0 X1
       have i₂ := eq20257 X0 sF0 x
       grind)
    | exact superpose eq20257 eq87
    | exact resolve eq87 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq21280 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ y) X1)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq20257 X0 sF2 sF4
       grind)
    | (have i₁ := eq91 X0 X1
       have i₂ := eq20257 X0 sF4 sF2
       grind)
    | exact superpose eq20257 eq91
    | exact resolve eq91 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq21518 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 (M.op X0 (M.op (M.op X1 X2) X1))) (M.op X0 X5)) = (M.op (M.op X3 X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq20407 X0 X1 X2 X3 X5
       have i₂ := eq2930 X0 X3 (M.op X1 X2) X1
       grind)
    | exact superpose eq2930 eq20407
    | exact resolve eq20407 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20407
  have eq22216 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op X4 (M.op X2 X3))) = (M.op (M.op (M.op X0 X3) X5) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20765 X0 X1 X2 X3 X4 X5
       have i₂ := eq20257 (M.op X0 X3) X5 (M.op X5 X4)
       grind)
    | (have i₁ := eq20765 X0 X1 X2 X3 X4 X5
       have i₂ := eq20257 (M.op X0 X3) (M.op X5 X4) X5
       grind)
    | exact superpose eq20257 eq20765
    | exact resolve eq20765 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20765
  have eq22322 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2)))) (M.op X0 X5)) = (M.op (M.op X3 X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq21518 X0 X1 X2 X3 X5
       have i₂ := eq3291 X3 (M.op X1 X2) X1 X0
       grind)
    | (have i₁ := eq21518 X0 X1 X2 X3 X5
       have i₂ := eq3291 X3 X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq3291 eq21518
    | exact resolve eq21518 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21518
  have eq22857 : ∀ X0 X2 X3 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X0 X5)) = (M.op (M.op X3 X2) X5) := by
    intro X0 X2 X3 X5
    first
    | (have i₁ := eq22322 X0 x X2 X3 X5
       have i₂ := eq3292 X0 X2 x
       grind)
    | exact superpose eq3292 eq22322
    | exact resolve eq22322 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22322
  have eq24552 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19531 eq14
    | (have j0 := eq14 y (M.op x y)
       grind)
    | exact resolve eq14 eq19531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24554 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq24552
  have eq26183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op X3 (M.op (σ y) X1))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq21280 eq572
    | exact resolve eq572 eq21280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq26764 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (M.op X1 (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3441 X0 x x
       have i₂ := eq26183 sF4 (M.op X0 (M.op x sF3)) x x
       grind)
    | exact superpose eq26183 eq3441
    | exact resolve eq3441 eq26183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441 eq26183
  have eq27090 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X1 (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq3084 eq26764
    | exact resolve eq26764 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26764
  have eq28807 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq3075 eq3288
    | exact resolve eq3288 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29316 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op x (M.op y x))) := by
    intro X0 X1
    first
    | exact superpose eq2925 eq28807
    | exact resolve eq28807 eq2925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925 eq28807
  have eq29723 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op X0 (M.op X1 (M.op x y))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq29316 X0 X1
       have i₂ := eq1983 (M.op X0 (M.op X1 sF0)) x y
       grind)
    | exact superpose eq1983 eq29316
    | exact resolve eq29316 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29316
  have eq29942 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op (M.op X0 y) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq29723 X0 X1
       have i₂ := eq20257 X0 y (M.op X1 sF0)
       grind)
    | (have i₁ := eq29723 X0 X1
       have i₂ := eq20257 X0 (M.op X1 sF0) y
       grind)
    | exact superpose eq20257 eq29723
    | exact resolve eq29723 eq20257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20257 eq29723
  have eq32090 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X4) = (M.op (M.op (M.op X0 (M.op X3 X2)) X5) (M.op X5 (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3953 (M.op X0 (M.op X3 X2)) X1 X4 X5
       have i₂ := eq3288 X3 X0 X1 X2
       grind)
    | (have i₁ := eq3953 (M.op X0 (M.op X3 X2)) X1 X4 X5
       have i₂ := eq3288 X1 X0 X3 X2
       grind)
    | exact superpose eq3288 eq3953
    | exact resolve eq3953 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32323 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) = (M.op X0 (M.op (M.op X1 X2) (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3953 (M.op (M.op X0 X1) X2) X3 X4 (M.op X1 X2)
       have i₂ := eq580 X0 X1 X2
       grind)
    | exact superpose eq580 eq3953
    | exact resolve eq3953 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32358 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 X0))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq3084 eq3953
    | exact resolve eq3953 eq3084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32664 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X1)) X4) = (M.op (M.op X3 (M.op X0 X4)) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3953 X3 (M.op X2 X1) X4 (M.op X0 X4)
       have i₂ := eq3953 X0 X1 X2 X4
       grind)
    | exact superpose eq3953 eq3953
    | exact resolve eq3953 eq3953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32950 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X1)) X4) = (M.op (M.op X3 (M.op X0 X4)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq32664 X0 X1 X2 X3 X4
       have i₂ := eq2930 X0 (M.op X3 (M.op X0 X4)) X1 X2
       grind)
    | exact superpose eq2930 eq32664
    | exact resolve eq32664 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32664
  have eq33176 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) X1) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq2926 eq32358
    | exact resolve eq32358 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32358
  have eq33186 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) = (M.op X0 (M.op X1 (M.op X2 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq32323 X0 X1 X2 X3 X4
       have i₂ := eq2930 X1 X0 X2 (M.op X4 X3)
       grind)
    | exact superpose eq2930 eq32323
    | exact resolve eq32323 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32323
  have eq33373 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X1)) X4) = (M.op (M.op X3 X4) (M.op X1 X2)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq32950 x X1 X2 X3 X4
       have i₂ := eq22857 x X4 X3 (M.op X1 X2)
       grind)
    | exact superpose eq22857 eq32950
    | exact resolve eq32950 eq22857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32950
  have eq36166 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op (M.op X0 X1) (M.op (σ y) X1))) (M.op X3 (M.op X0 (σ x)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq21280 eq4030
    | exact resolve eq4030 eq21280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21280
  have eq36290 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4030 X2 X3 X0 (M.op X3 X1)
       have i₂ := eq3292 X0 X1 X3
       grind)
    | exact superpose eq3292 eq4030
    | exact resolve eq4030 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36612 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X1) = (M.op (M.op X3 (M.op X0 (M.op X4 X2))) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3953 X3 X4 X1 (M.op X0 (M.op X4 X2))
       have i₂ := eq4030 X1 X4 X0 X2
       grind)
    | exact superpose eq4030 eq3953
    | exact resolve eq3953 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030
  have eq36658 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X1) = (M.op (M.op X3 (M.op X0 (M.op X4 X2))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq36612 X0 X1 X2 X3 X4
       have i₂ := eq2930 X0 (M.op X3 (M.op X0 (M.op X4 X2))) X1 X2
       grind)
    | exact superpose eq2930 eq36612
    | exact resolve eq36612 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36612
  have eq37215 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op X0 (σ x))) (M.op (M.op (M.op X0 X1) (M.op (σ y) X1)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36166 X0 X1 X0 X2
       have i₂ := eq36290 X0 (M.op (M.op X0 X1) (M.op sF3 X1)) X2 (M.op X0 sF2)
       grind)
    | (have i₁ := eq36166 X0 X1 X0 X3
       have i₂ := eq36290 X0 (M.op X0 sF2) (M.op (M.op X0 X1) (M.op sF3 X1)) X3
       grind)
    | exact superpose eq36290 eq36166
    | exact resolve eq36166 eq36290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36166
  have eq37385 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X1) = (M.op (M.op X3 (M.op X4 X2)) (M.op X1 X2)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq36658 x X1 X2 X3 X4
       have i₂ := eq22857 x (M.op X4 X2) X3 (M.op X1 X2)
       grind)
    | exact superpose eq22857 eq36658
    | exact resolve eq36658 eq22857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36658
  have eq37795 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op X0 (σ x))) (M.op (M.op X0 X1) (M.op (M.op (σ y) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37215 X0 X1 X2 X3
       have i₂ := eq2930 (M.op X0 X1) (M.op X2 (M.op X0 sF2)) (M.op sF3 X1) X3
       grind)
    | exact superpose eq2930 eq37215
    | exact resolve eq37215 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37215
  have eq37936 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X1) = (M.op (M.op X3 X2) (M.op (M.op X4 X2) X1)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq37385 X1 X2 X3 X4
       have i₂ := eq36290 X3 X2 (M.op X4 X2) X1
       grind)
    | (have i₁ := eq37385 X2 X3 x X4
       have i₂ := eq36290 x (M.op X4 X3) X2 X3
       grind)
    | exact superpose eq36290 eq37385
    | exact resolve eq37385 eq36290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37385
  have eq38197 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op X0 (σ x))) (M.op X0 (M.op X1 (M.op (M.op (σ y) X1) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37795 X0 X2 X2 X3
       have i₂ := eq2930 X0 (M.op X2 (M.op X0 sF2)) X2 (M.op (M.op sF3 X2) X3)
       grind)
    | exact superpose eq2930 eq37795
    | exact resolve eq37795 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37795
  have eq38255 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X1) = (M.op (M.op X3 X2) (M.op X4 (M.op X2 X1))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq37936 X1 X2 X3 X4
       have i₂ := eq2930 X4 (M.op X3 X2) X2 X1
       grind)
    | exact superpose eq2930 eq37936
    | exact resolve eq37936 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37936
  have eq38431 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ x) (σ y))) = (M.op (M.op X2 (σ x)) (M.op X1 (M.op (M.op (σ y) X1) X3))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq38197 x X1 X3 X3
       have i₂ := eq22857 x sF2 X3 (M.op X1 (M.op (M.op sF3 X1) X3))
       grind)
    | exact superpose eq22857 eq38197
    | exact resolve eq38197 eq22857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38197
  have eq38564 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ x) (σ y))) = (M.op (M.op X2 (σ x)) (M.op X1 (M.op (σ y) (M.op X1 X3)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq38431 X2 X2 X3
       have i₂ := eq2930 sF3 X2 X2 X3
       grind)
    | exact superpose eq2930 eq38431
    | exact resolve eq38431 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38431
  have eq43332 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X0)) = (M.op X1 (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq27090 eq3292
    | exact resolve eq3292 eq27090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43336 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (M.op X2 (M.op (σ y) (M.op X0 (M.op X1 (σ y)))))) X1) = (M.op (M.op (σ x) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq27090 eq3288
    | exact resolve eq3288 eq27090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27090
  have eq43376 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (M.op (σ x) X1) (M.op (M.op (σ y) (M.op X0 (M.op X1 (σ y)))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43336 X0 x X2
       have i₂ := eq33373 (M.op sF3 (M.op X0 (M.op x sF3))) X2 sF2 x
       grind)
    | (have i₁ := eq43336 X0 (M.op X1 X2) X2
       have i₂ := eq33373 X1 X2 sF2 (M.op X2 (M.op sF3 (M.op X0 (M.op (M.op X1 X2) sF3))))
       grind)
    | exact superpose eq33373 eq43336
    | exact resolve eq43336 eq33373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33373 eq43336
  have eq43379 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X0)) = (M.op X1 (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq43332
    | (have j0 := eq43332 X0 X1
       grind)
    | exact resolve eq43332 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43332
  have eq43451 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (M.op (σ x) X1) (M.op (σ y) (M.op (M.op X0 (M.op X1 (σ y))) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43376 X0 X1 x
       have i₂ := eq2930 sF3 (M.op sF2 X1) (M.op X0 (M.op X1 sF3)) x
       grind)
    | exact superpose eq2930 eq43376
    | exact resolve eq43376 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43376
  have eq43520 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (M.op X0 (M.op X1 (σ y))) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq12664 eq43451
    | exact resolve eq43451 eq12664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12664 eq43451
  have eq43569 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (M.op X1 (σ y)) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43520 X0 X1 x
       have i₂ := eq2930 X0 X1 (M.op X1 sF3) x
       grind)
    | exact superpose eq2930 eq43520
    | exact resolve eq43520 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43520
  have eq43595 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) X0) X2) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op X1 (M.op (σ y) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43569 X1 X0 x
       have i₂ := eq2930 X0 X1 sF3 x
       grind)
    | exact superpose eq2930 eq43569
    | exact resolve eq43569 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43569
  have eq46256 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X3 X6) (M.op (M.op X5 X1) X6)) X7) (M.op X7 (M.op (M.op (M.op X0 X4) (M.op X2 X4)) X5))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq3309 X3 X6 (M.op X5 X1) (M.op (M.op (M.op X0 X4) (M.op X2 X4)) X5) X7
       have i₂ := eq3309 X0 X4 X2 X1 X5
       grind)
    | exact superpose eq3309 eq3309
    | exact resolve eq3309 eq3309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46719 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 x) (M.op x y)) X3) (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3309 X0 x y X1 X3
       have i₂ := eq20888 X0 x
       grind)
    | exact superpose eq20888 eq3309
    | exact resolve eq3309 eq20888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888
  have eq46783 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X2 X3) X4)) = (M.op (M.op (M.op (M.op X1 X5) (M.op X4 X5)) (M.op (M.op X0 X2) X3)) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3309 X1 X5 X4 (M.op X2 X3) (M.op (M.op X0 X2) X3)
       have i₂ := eq580 X0 X2 X3
       grind)
    | exact superpose eq580 eq3309
    | exact resolve eq3309 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46992 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) (M.op X3 X4))) = (M.op X5 (M.op X0 (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3291 X5 X2 X4 X0
       have i₂ := eq3309 X0 X1 X2 X4 X3
       grind)
    | exact superpose eq3309 eq3291
    | exact resolve eq3291 eq3309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291
  have eq47082 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X1)) = (M.op X3 (M.op (M.op (M.op (M.op X0 X5) (M.op X2 X5)) X4) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3292 X3 (M.op X4 X1) (M.op (M.op (M.op X0 X5) (M.op X2 X5)) X4)
       have i₂ := eq3309 X0 X5 X2 X1 X4
       grind)
    | exact superpose eq3309 eq3292
    | exact resolve eq3292 eq3309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq47102 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X1)) = (M.op X3 (M.op (M.op (M.op X0 X5) (M.op X2 X5)) (M.op X4 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq47082 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 (M.op (M.op X0 X5) (M.op X2 X5)) X3 X4 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq2930 eq47082
    | exact resolve eq47082 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47082
  have eq47181 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op X0 (M.op X2 X4))) = (M.op X5 (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X3 (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq46992 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 (M.op (M.op X0 X1) (M.op X2 X1)) X5 X3 (M.op X3 X4)
       grind)
    | exact superpose eq2930 eq46992
    | exact resolve eq46992 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46992
  have eq47382 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X3) X4)) = (M.op X1 (M.op (M.op (M.op X0 X2) X3) (M.op X0 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq46783 X0 X1 X2 X3 X4 x
       have i₂ := eq3326 X1 x X4 (M.op (M.op X0 X2) X3) X0
       grind)
    | exact superpose eq3326 eq46783
    | exact resolve eq46783 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326 eq46783
  have eq47680 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X3 X6) (M.op X5 X6)) (M.op X5 X1)) (M.op (M.op X0 X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq46256 X0 X1 X2 X3 X4 X5 X6 x
       have i₂ := eq32090 (M.op X3 X6) X5 X6 (M.op X5 X1) (M.op (M.op X0 X4) (M.op X2 X4)) x
       grind)
    | exact superpose eq32090 eq46256
    | exact resolve eq46256 eq32090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32090 eq46256
  have eq47701 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X1)) = (M.op X3 (M.op (M.op X0 X5) (M.op (M.op X2 X5) (M.op X4 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq47102 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 (M.op X0 X5) X3 (M.op X2 X5) (M.op X4 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq2930 eq47102
    | exact resolve eq47102 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47102
  have eq47764 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op X0 (M.op X2 X4))) = (M.op X5 (M.op (M.op X0 X1) (M.op (M.op X2 X1) (M.op X3 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq47181 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 (M.op X0 X1) X5 (M.op X2 X1) (M.op X3 (M.op X3 X4))
       grind)
    | exact superpose eq2930 eq47181
    | exact resolve eq47181 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47181
  have eq47949 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X3) X4)) = (M.op X1 (M.op (M.op X0 X2) (M.op X3 (M.op X0 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq47382 X0 X1 X2 X3 X4
       have i₂ := eq2930 (M.op X0 X2) X1 X3 (M.op X0 X4)
       grind)
    | exact superpose eq2930 eq47382
    | exact resolve eq47382 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47382
  have eq48140 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X3 X6) (M.op X5 X6)) (M.op X5 X1)) (M.op X0 (M.op X4 (M.op X2 X4)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq47680 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq2930 X0 (M.op (M.op (M.op X3 X6) (M.op X5 X6)) (M.op X5 X1)) X4 (M.op X2 X4)
       grind)
    | exact superpose eq2930 eq47680
    | exact resolve eq47680 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47680
  have eq48159 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X1)) = (M.op X3 (M.op X0 (M.op X5 (M.op (M.op X2 X5) (M.op X4 (M.op X0 (M.op X1 X2))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq47701 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 X0 X3 X5 (M.op (M.op X2 X5) (M.op X4 (M.op X0 (M.op X1 X2))))
       grind)
    | exact superpose eq2930 eq47701
    | exact resolve eq47701 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47701
  have eq48214 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op X0 (M.op X2 X4))) = (M.op X5 (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X3 (M.op X3 X4)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq47764 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 X0 X5 X1 (M.op (M.op X2 X1) (M.op X3 (M.op X3 X4)))
       grind)
    | exact superpose eq2930 eq47764
    | exact resolve eq47764 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47764
  have eq48370 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X3) X4)) = (M.op X1 (M.op X0 (M.op X2 (M.op X3 (M.op X0 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq47949 X0 X1 X2 X3 X4
       have i₂ := eq2930 X0 X1 X2 (M.op X3 (M.op X0 X4))
       grind)
    | exact superpose eq2930 eq47949
    | exact resolve eq47949 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47949
  have eq48496 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X3 X6) (M.op X5 X6)) (M.op X5 X1)) (M.op X0 X2)) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq48140 X0 X1 X2 X3 x X5 X6
       have i₂ := eq1983 X0 x X2
       grind)
    | exact superpose eq1983 eq48140
    | exact resolve eq48140 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48140
  have eq48512 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X1)) = (M.op X3 (M.op X0 (M.op X5 (M.op X2 (M.op X5 (M.op X4 (M.op X0 (M.op X1 X2)))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq48159 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 X2 X5 X5 (M.op X4 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq2930 eq48159
    | exact resolve eq48159 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48159
  have eq48557 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op X0 (M.op X2 X4))) = (M.op X5 (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X3 (M.op X3 X4))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq48214 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 X2 X1 X1 (M.op X3 (M.op X3 X4))
       grind)
    | exact superpose eq2930 eq48214
    | exact resolve eq48214 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48214
  have eq48665 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 X4))) = (M.op X1 (M.op X0 (M.op X2 (M.op X3 (M.op X0 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq48370 X0 X1 X2 X3 X4
       have i₂ := eq2930 X2 X1 X3 X4
       grind)
    | exact superpose eq2930 eq48370
    | exact resolve eq48370 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48370
  have eq48737 : ∀ X0 X1 X2 X3 X6 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X3 X6) X6) X1) (M.op X0 X2)) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq48496 X0 X1 X2 X3 x X6
       have i₂ := eq22857 x X6 (M.op X3 X6) X1
       grind)
    | exact superpose eq22857 eq48496
    | exact resolve eq48496 eq22857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48496
  have eq48781 : ∀ X0 X1 X2 X4 X5 : G, (M.op X5 (M.op X0 (M.op X2 X4))) = (M.op X5 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X4))))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq48557 X0 X1 X2 x X4 X5
       have i₂ := eq3292 X1 X4 x
       grind)
    | exact superpose eq3292 eq48557
    | exact resolve eq48557 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48557
  have eq48972 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X1)) = (M.op X3 (M.op X0 (M.op X2 (M.op X4 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq48512 X0 X1 X2 X3 X4 x
       have i₂ := eq48781 X0 x X2 (M.op X4 (M.op X0 (M.op X1 X2))) X3
       grind)
    | exact superpose eq48781 eq48512
    | exact resolve eq48512 eq48781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48512 eq48781
  have eq49131 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X1)) = (M.op X3 (M.op X2 (M.op X4 (M.op X1 X2)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq48972 x X1 X2 X3 X4
       have i₂ := eq48665 x X3 X2 X4 (M.op X1 X2)
       grind)
    | exact superpose eq48665 eq48972
    | exact resolve eq48972 eq48665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48665 eq48972
  have eq50739 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 (M.op X3 X2)) (M.op X4 X5)) = (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X3) X4) X6) (M.op X1 (M.op X5 X6))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3422 (M.op X0 (M.op X3 X2)) X1 X4 X6 X5
       have i₂ := eq3288 X3 X0 X1 X2
       grind)
    | (have i₁ := eq3422 (M.op X0 (M.op X3 X2)) X1 X4 X6 X5
       have i₂ := eq3288 X1 X0 X3 X2
       grind)
    | exact superpose eq3288 eq3422
    | exact resolve eq3422 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50944 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X3 (M.op X2 X1)) X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X5) (M.op X3 (M.op X4 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3422 X0 X3 (M.op X3 (M.op X2 X1)) X5 X4
       have i₂ := eq3953 X0 X1 X2 X3
       grind)
    | exact superpose eq3953 eq3422
    | exact resolve eq3422 eq3953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51271 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op (M.op (M.op (M.op X2 X0) X3) (M.op X4 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3422 X2 X0 X3 (M.op X4 X1) X4
       have i₂ := eq3292 X0 X1 X4
       grind)
    | exact superpose eq3292 eq3422
    | exact resolve eq3422 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq51525 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X2 (M.op X0 (M.op X3 (M.op (M.op X0 X1) (M.op X4 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51271 X0 X1 X2 X3 X4
       have i₂ := eq33186 X2 X0 X3 (M.op X4 X1) (M.op X0 X1)
       grind)
    | exact superpose eq33186 eq51271
    | exact resolve eq51271 eq33186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51271
  have eq51787 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X5) (M.op X3 (M.op X4 X5))) = (M.op X0 (M.op X3 (M.op (M.op X2 X1) X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq50944 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 X3 X0 (M.op X2 X1) X4
       grind)
    | exact superpose eq2930 eq50944
    | exact resolve eq50944 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50944
  have eq52026 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X2 (M.op X0 (M.op X3 (M.op X0 (M.op X1 (M.op X4 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51525 X0 X1 X2 X3 X4
       have i₂ := eq2930 X0 X3 X1 (M.op X4 X1)
       grind)
    | exact superpose eq2930 eq51525
    | exact resolve eq51525 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51525
  have eq52253 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X5) (M.op X3 (M.op X4 X5))) = (M.op X0 (M.op X3 (M.op X2 (M.op X1 X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq51787 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 X2 X3 X1 X4
       grind)
    | exact superpose eq2930 eq51787
    | exact resolve eq51787 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51787
  have eq52384 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 X4)) = (M.op X2 (M.op X0 (M.op X3 (M.op X0 X4)))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq52026 X0 x X2 X3 X4
       have i₂ := eq1983 X0 x X4
       grind)
    | exact superpose eq1983 eq52026
    | exact resolve eq52026 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52026
  have eq52564 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X3 X2)) (M.op X4 X5)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X1 (M.op X4 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq50739 X0 X1 X2 X3 X4 X5 x
       have i₂ := eq52253 (M.op X0 (M.op X1 X2)) X3 X4 X1 X5 x
       grind)
    | exact superpose eq52253 eq50739
    | exact resolve eq50739 eq52253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50739 eq52253
  have eq52662 : ∀ X2 X3 : G, (M.op (M.op X2 X3) (M.op (σ x) (σ y))) = (M.op (M.op X2 (σ x)) (M.op (σ y) X3)) := by
    intro X2 X3
    first
    | (have i₁ := eq38564 x X2 x
       have i₂ := eq52384 x (M.op X2 sF2) sF3 x
       grind)
    | exact superpose eq52384 eq38564
    | exact resolve eq38564 eq52384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38564
  have eq52721 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X2))) = (M.op (M.op (σ x) X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq43595 x X0 X2
       have i₂ := eq52384 X0 sF4 x (M.op sF3 X2)
       grind)
    | exact superpose eq52384 eq43595
    | exact resolve eq43595 eq52384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43595
  have eq52913 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X3 X2)) (M.op X4 X5)) = (M.op (M.op X0 X2) (M.op X4 (M.op X3 X5))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq52564 X0 x X2 X3 X4 X5
       have i₂ := eq22857 x X2 X0 (M.op X4 (M.op X3 X5))
       grind)
    | exact superpose eq22857 eq52564
    | exact resolve eq52564 eq22857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22857 eq52564
  have eq57231 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X4)) X5) (M.op X5 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20775 (M.op (M.op X0 X1) X2) (M.op X1 X2) X4 X3 X5
       have i₂ := eq580 X0 X1 X2
       grind)
    | exact superpose eq580 eq20775
    | exact resolve eq20775 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57447 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X0 X3) X4)) X0) X5) (M.op X5 (M.op (M.op X3 X4) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20775 X1 (M.op (M.op X0 X3) X4) (M.op X3 X4) X2 X5
       have i₂ := eq580 X0 X3 X4
       grind)
    | exact superpose eq580 eq20775
    | exact resolve eq20775 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq20775
  have eq58591 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X0 X3) X4)) X0) X5) (M.op X5 (M.op X3 (M.op X4 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq57447 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 X3 X5 X4 X2
       grind)
    | exact superpose eq2930 eq57447
    | exact resolve eq57447 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57447
  have eq58761 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X4))) X5) (M.op X5 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq57231 X0 X1 X2 X3 X4 X5
       have i₂ := eq2930 X1 X0 X2 X4
       grind)
    | exact superpose eq2930 eq57231
    | exact resolve eq57231 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57231
  have eq59304 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 (M.op X0 X4)) (M.op X0 X3)) X5) (M.op X5 (M.op X3 (M.op X4 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq58591 X0 X1 X2 X3 X4 X5
       have i₂ := eq3288 (M.op X0 X3) X1 X0 X4
       grind)
    | (have i₁ := eq58591 X0 X1 X2 X3 X4 X5
       have i₂ := eq3288 X0 X1 (M.op X0 X3) X4
       grind)
    | exact superpose eq3288 eq58591
    | exact resolve eq58591 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288 eq58591
  have eq59944 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 X4) (M.op X0 (M.op X0 X3))) X5) (M.op X5 (M.op X3 (M.op X4 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq59304 X0 X1 X2 X3 X4 X5
       have i₂ := eq52913 X1 X4 X0 X0 X3
       grind)
    | exact superpose eq52913 eq59304
    | exact resolve eq59304 eq52913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59304
  have eq60437 : ∀ X0 X1 X2 X4 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 X4) X0) X0) (M.op X4 X2)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq59944 X0 X1 X2 x X4 x
       have i₂ := eq58761 (M.op X1 X4) X0 X0 (M.op X4 X2) x x
       grind)
    | exact superpose eq58761 eq59944
    | exact resolve eq59944 eq58761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58761 eq59944
  have eq97197 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 (M.op (M.op X0 X6) (M.op X6 X5))) (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3953 X4 (M.op X5 X1) X3 (M.op (M.op X0 X6) (M.op X6 X5))
       have i₂ := eq22216 X0 X6 X5 X1 X3 X2
       grind)
    | (have i₁ := eq3953 X0 X4 X5 (M.op (M.op X0 X3) X5)
       have i₂ := eq22216 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq22216 eq3953
    | exact resolve eq3953 eq22216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953 eq22216
  have eq97424 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 (M.op (M.op X0 X6) (M.op X6 X5))) (M.op (M.op X0 X1) (M.op X2 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq97197 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq2930 (M.op X0 X1) (M.op X4 (M.op (M.op X0 X6) (M.op X6 X5))) X2 (M.op X2 X3)
       grind)
    | exact superpose eq2930 eq97197
    | exact resolve eq97197 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97197
  have eq99075 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 (M.op (M.op X0 X6) (M.op X6 X5))) (M.op X0 (M.op X1 (M.op X2 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq97424 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq2930 X0 (M.op X4 (M.op (M.op X0 X6) (M.op X6 X5))) X1 (M.op X2 (M.op X2 X3))
       grind)
    | exact superpose eq2930 eq97424
    | exact resolve eq97424 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97424
  have eq100559 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 (M.op X6 X5)) (M.op X0 (M.op (M.op X0 X6) (M.op X1 (M.op X2 (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq99075 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq52913 X4 (M.op X6 X5) (M.op X0 X6) X0 (M.op X1 (M.op X2 (M.op X2 X3)))
       grind)
    | exact superpose eq52913 eq99075
    | exact resolve eq99075 eq52913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99075
  have eq101753 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 (M.op X6 X5)) (M.op X0 (M.op X0 (M.op X6 (M.op X1 (M.op X2 (M.op X2 X3))))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq100559 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq2930 X0 X0 X6 (M.op X1 (M.op X2 (M.op X2 X3)))
       grind)
    | exact superpose eq2930 eq100559
    | exact resolve eq100559 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100559
  have eq102706 : ∀ X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 (M.op X6 X5)) (M.op X6 (M.op X1 (M.op X2 (M.op X2 X3))))) := by
    intro X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq101753 x X1 X2 X3 X4 X5 X6
       have i₂ := eq3292 (M.op X4 (M.op X6 X5)) (M.op X6 (M.op X1 (M.op X2 (M.op X2 X3)))) x
       grind)
    | exact superpose eq3292 eq101753
    | exact resolve eq101753 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101753
  have eq103468 : ∀ X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 X5) (M.op X6 (M.op X6 (M.op X1 (M.op X2 (M.op X2 X3)))))) := by
    intro X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq102706 X1 X2 X3 X4 X5 X6
       have i₂ := eq52913 X4 X5 X6 X6 (M.op X1 (M.op X2 (M.op X2 X3)))
       grind)
    | exact superpose eq52913 eq102706
    | exact resolve eq102706 eq52913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52913 eq102706
  have eq104060 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 X5) (M.op X1 (M.op X2 (M.op X2 X3)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq103468 X1 X2 X3 X4 X5 x
       have i₂ := eq3292 (M.op X4 X5) (M.op X1 (M.op X2 (M.op X2 X3))) x
       grind)
    | exact superpose eq3292 eq103468
    | exact resolve eq103468 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103468
  have eq104523 : ∀ X1 X3 X4 X5 : G, (M.op (M.op X4 (M.op X5 X1)) X3) = (M.op (M.op X4 X5) (M.op X1 X3)) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq104060 X1 x X3 X4 X5
       have i₂ := eq3292 X1 X3 x
       grind)
    | exact superpose eq3292 eq104060
    | exact resolve eq104060 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104060
  have eq105148 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X2)) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10372 x X1 x
       have i₂ := eq104523 sF3 x sF4 x
       grind)
    | exact superpose eq104523 eq10372
    | exact resolve eq10372 eq104523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10372
  have eq107246 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (M.op X2 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105148 X0 X1 X1
       have i₂ := eq104523 X1 (M.op X1 (M.op X0 X1)) (M.op sF4 X0) sF3
       grind)
    | exact superpose eq104523 eq105148
    | exact resolve eq105148 eq104523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104523 eq105148
  have eq108300 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq107246 X1 x x
       have i₂ := eq49131 X1 x (M.op (M.op sF4 X1) sF3) x
       grind)
    | exact superpose eq49131 eq107246
    | exact resolve eq107246 eq49131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49131 eq107246
  have eq519415 : x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15583 eq24554
    | exact resolve eq24554 eq15583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519417 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24554 eq15583
    | exact resolve eq15583 eq24554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15583 eq24554
  have eq519432 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq519417
  have eq519433 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq519415
  have eq520459 : y ≠ y ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq519432 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq519432
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq519432
       grind)
    | exact resolve eq13 eq519432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519432
  have eq520575 : y ≠ y ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq520459
  have eq520576 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq520575
  have eq520790 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq520576 eq19524
    | exact resolve eq19524 eq520576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19524
  have eq520791 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq520576 eq19531
    | exact resolve eq19531 eq520576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19531 eq520576
  have eq520851 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq520791
  have eq520852 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq520790
  have eq520870 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq520852
       have r₂ := eq118
       grind)
    | exact resolve eq520852 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq520852
  have eq520872 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq520851 eq20
    | exact resolve eq20 eq520851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520882 : x = (M.op (M.op y x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq520851 eq3075
    | exact resolve eq3075 eq520851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq520885 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq520851 eq3883
    | exact resolve eq3883 eq520851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3883
  have eq520955 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq520851
  have eq520960 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq520885 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq520885
    | (have j0 := eq520885 X0
       grind)
    | exact resolve eq520885 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520885
  have eq520962 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq520872
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq520872
    | exact resolve eq520872 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520872
  have eq520963 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq520962 eq26
    | exact resolve eq26 eq520962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520977 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq520962 eq756
    | (have r₁ := eq756
       have r₂ := eq520962
       grind)
    | exact resolve eq756 eq520962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq520962
  have eq521712 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq520977
  have eq521713 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq521712
  have eq521738 : (σ x) ≠ (σ x) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq521713 eq117
    | (have r₁ := eq117
       have r₂ := eq521713
       grind)
    | exact resolve eq117 eq521713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq521768 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq521713 eq3084
    | exact resolve eq3084 eq521713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084
  have eq521815 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq521713 eq7798
    | exact resolve eq7798 eq521713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523216 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq521738
  have eq523241 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq521815 X0
       have i₂ := eq3287 X0 sF3 sF2
       grind)
    | (have i₁ := eq521815 X0
       have i₂ := eq3287 X0 sF2 sF3
       grind)
    | exact superpose eq3287 eq521815
    | exact resolve eq521815 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521815
  have eq523244 : (σ x) = (M.op (M.op (σ x) x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq521768
       have i₂ := eq3639 sF2 sF2
       grind)
    | exact superpose eq3639 eq521768
    | exact resolve eq521768 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639 eq521768
  have eq523254 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq523241
    | (have j0 := eq523241 X0
       grind)
    | exact resolve eq523241 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523241
  have eq523255 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ y) x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52721 eq523244
    | exact resolve eq523244 eq52721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523244
  have eq523264 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq523255
       have i₂ := eq1983 sF4 x sF3
       grind)
    | exact superpose eq1983 eq523255
    | exact resolve eq523255 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523255
  have eq523436 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq520963 eq3292
    | exact resolve eq3292 eq520963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520963
  have eq523701 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3880 eq523436
    | exact resolve eq523436 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523436
  have eq527797 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) y) (M.op (σ y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq520960 eq579
    | exact resolve eq579 eq520960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520960
  have eq528429 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29942 eq527797
    | exact resolve eq527797 eq29942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29942 eq527797
  have eq529862 : (σ x) = (M.op (M.op (σ x) x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq521713 eq528429
    | exact resolve eq528429 eq521713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521713 eq528429
  have eq530109 : (σ x) = (M.op (M.op (σ x) x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq529862
  have eq530207 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op (σ y) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52721 eq530109
    | exact resolve eq530109 eq52721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530109
  have eq530279 : (σ x) = (M.op (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq530207
       have i₂ := eq2981 x sF4 sF3
       grind)
    | exact superpose eq2981 eq530207
    | exact resolve eq530207 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981 eq530207
  have eq530551 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq530279 eq3292
    | exact resolve eq3292 eq530279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530279
  have eq530860 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2926 eq530551
    | exact resolve eq530551 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926 eq530551
  have eq530927 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq530860 X0
       have i₂ := eq1983 X0 sF2 sF3
       grind)
    | exact superpose eq1983 eq530860
    | exact resolve eq530860 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530860
  have eq532055 : x = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq523254 eq3020
    | exact resolve eq3020 eq523254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020 eq523254
  have eq532977 : x = (M.op (M.op (M.op x y) y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq532055
       have i₂ := eq36290 sF0 sF2 sF4 y
       grind)
    | (have i₁ := eq532055
       have i₂ := eq36290 sF0 y sF2 sF4
       grind)
    | exact superpose eq36290 eq532055
    | exact resolve eq532055 eq36290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36290 eq532055
  have eq533148 : x = (M.op (M.op (M.op x y) y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3880 eq532977
    | exact resolve eq532977 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880 eq532977
  have eq540777 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq530927 eq523701
    | exact resolve eq523701 eq530927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530927
  have eq542012 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq540777 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540777
  have eq544239 : x = (M.op (M.op y y) (σ y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq519433 eq533148
    | exact resolve eq533148 eq519433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519433 eq533148
  have eq544468 : x = (M.op (M.op y y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq544239
  have eq544573 : x = (M.op (M.op y y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq544468
       have r₂ := eq520955
       grind)
    | exact resolve eq544468 eq520955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520955 eq544468
  have eq563255 : x = (M.op (M.op y y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq544573 eq523701
    | exact resolve eq523701 eq544573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523701 eq544573
  have eq563371 : x = (M.op (M.op y y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq563255
  have eq575063 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq523216
       have i₂ := eq520870
       grind)
    | exact superpose eq520870 eq523216
    | exact resolve eq523216 eq520870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520870 eq523216
  have eq575162 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq575063
  have eq575164 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq575162
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq575162
    | exact resolve eq575162 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575162
  have eq575260 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq575164 eq20835
    | exact resolve eq20835 eq575164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20835
  have eq575488 : (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq575164 eq108300
    | exact resolve eq108300 eq575164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108300 eq575164
  have eq575670 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33176 eq575488
    | exact resolve eq575488 eq33176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33176 eq575488
  have eq575773 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52721 eq575260
    | exact resolve eq575260 eq52721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575260
  have eq575776 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq575670
       have i₂ := eq1983 sF2 sF3 sF3
       grind)
    | exact superpose eq1983 eq575670
    | exact resolve eq575670 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575670
  have eq575829 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq575773 x
       have i₂ := eq52384 x sF4 x (M.op sF3 (M.op x sF4))
       grind)
    | (have i₁ := eq575773 x
       have i₂ := eq52384 x sF4 sF3 sF4
       grind)
    | exact superpose eq52384 eq575773
    | exact resolve eq575773 eq52384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575773
  have eq575830 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq575776
    | exact resolve eq575776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq575776
  have eq575859 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7798 eq575829
    | exact resolve eq575829 eq7798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575829
  have eq576082 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq575830 eq52662
    | exact resolve eq52662 eq575830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52662 eq575830
  have eq576246 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52721 eq576082
    | exact resolve eq576082 eq52721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576082
  have eq576348 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43379 eq576246
    | exact resolve eq576246 eq43379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43379 eq576246
  have eq576407 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq576348
       have i₂ := eq3292 sF4 sF3 sF2
       grind)
    | exact superpose eq3292 eq576348
    | exact resolve eq576348 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576348
  have eq577143 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq576407 eq523264
    | exact resolve eq523264 eq576407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523264 eq576407
  have eq577378 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq577143
  have eq577999 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq577378 eq3009
    | exact resolve eq3009 eq577378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009 eq577378
  have eq578257 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52721 eq577999
    | exact resolve eq577999 eq52721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52721 eq577999
  have eq578317 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq578257 x
       have i₂ := eq52384 x sF4 x (M.op sF3 (M.op x sF4))
       grind)
    | (have i₁ := eq578257 x
       have i₂ := eq52384 x sF4 sF3 sF4
       grind)
    | exact superpose eq52384 eq578257
    | exact resolve eq578257 eq52384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578257
  have eq578347 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7798 eq578317
    | exact resolve eq578317 eq7798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7798 eq578317
  have eq580272 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq578347 eq575859
    | exact resolve eq575859 eq578347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575859 eq578347
  have eq580552 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq580272
  have eq583444 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq580552 eq12
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq580552
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq580552
       grind)
    | exact resolve eq12 eq580552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580552
  have eq583598 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq583444
  have eq583750 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70 eq583598
    | exact resolve eq583598 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq583598
  have eq588923 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq583750
       grind)
    | exact superpose eq583750 eq10
    | exact resolve eq10 eq583750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583750
  have eq588947 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq588923
    | exact resolve eq588923 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq588923
  have eq588951 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq588947
       grind)
    | exact superpose eq588947 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq588947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588947
  have eq588953 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq588951
  have eq588963 : x = (M.op y (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq563371
       have i₂ := eq588953
       grind)
    | exact superpose eq588953 eq563371
    | exact resolve eq563371 eq588953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563371 eq588953
  have eq589286 : x = (M.op y (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq588963
  have eq591439 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq589286 eq542012
    | exact resolve eq542012 eq589286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542012 eq589286
  have eq591586 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq591439
  have eq593429 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq520882
       have i₂ := eq591586
       grind)
    | exact superpose eq591586 eq520882
    | exact resolve eq520882 eq591586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520882 eq591586
  have eq593640 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq593429
  have eq593732 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq593640
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq593640
    | exact resolve eq593640 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593640
  have eq593733 : x = (M.op x y) := by grind
  clear eq593732
  have eq593766 : x = (M.op x y) := by
    first
    | exact superpose eq593733 eq18
    | exact resolve eq18 eq593733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq593767 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq593733 eq20
    | exact resolve eq20 eq593733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq593776 : x ≠ x ∨ (k y x) = (M.op x x) := by
    first
    | exact superpose eq593733 eq108
    | (have r₁ := eq108
       have r₂ := eq593733
       grind)
    | exact resolve eq108 eq593733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq593808 : (M.op x x) = (k (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq593733 eq2288
    | exact resolve eq2288 eq593733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2288
  have eq594024 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op (M.op (M.op X0 x) x) X3) (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | exact superpose eq593733 eq46719
    | exact resolve eq46719 eq593733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46719 eq593733
  have eq594699 : (k y x) = (M.op x x) := by grind
  clear eq593776
  have eq594846 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op X3 (M.op X3 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq594024 X0 X1 X3
       have i₂ := eq48737 X3 X3 X1 X0 x
       grind)
    | exact superpose eq48737 eq594024
    | exact resolve eq594024 eq48737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48737 eq594024
  have eq594961 : (σ y) = (σ (M.op x x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq594699
       grind)
    | exact superpose eq594699 eq129
    | exact resolve eq129 eq594699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq594962 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq341
       have i₂ := eq594699
       grind)
    | exact superpose eq594699 eq341
    | exact resolve eq341 eq594699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq594699
  have eq595004 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq593767
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq593767
    | exact resolve eq593767 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq593767
  have eq595117 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq594846 X0 X1 x
       have i₂ := eq3292 X0 X1 x
       grind)
    | exact superpose eq3292 eq594846
    | exact resolve eq594846 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594846
  have eq595210 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq595004 eq579
    | exact resolve eq579 eq595004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq595224 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq595004 eq3023
    | exact resolve eq3023 eq595004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023
  have eq596040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq595004 eq594961
    | exact resolve eq594961 eq595004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594961
  have eq596041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq595004 eq594962
    | exact resolve eq594962 eq595004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594962 eq595004
  have eq596245 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq596041
       have r₂ := eq27
       grind)
    | exact resolve eq596041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596041
  have eq596246 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq596040
       have r₂ := eq27
       grind)
    | exact resolve eq596040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596040
  have eq597465 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op X0 x) X1) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq60437 X1 X0 y x
       have i₂ := eq593766
       grind)
    | exact superpose eq593766 eq60437
    | exact resolve eq60437 eq593766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60437 eq593766
  have eq597518 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op X1 (M.op x X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq597465 X0 X1
       have i₂ := eq33186 X0 x X1 X1 x
       grind)
    | exact superpose eq33186 eq597465
    | exact resolve eq597465 eq33186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33186 eq597465
  have eq597598 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq597518 X0 X1
       have i₂ := eq52384 x X0 X1 X1
       grind)
    | (have i₁ := eq597518 x X1
       have i₂ := eq52384 X0 x x (M.op X1 (M.op x X1))
       grind)
    | exact superpose eq52384 eq597518
    | exact resolve eq597518 eq52384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52384 eq597518
  have eq601303 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3287 X0 y X1
       have i₂ := eq595117 X0 X1
       grind)
    | exact superpose eq595117 eq3287
    | exact resolve eq3287 eq595117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287 eq595117
  have eq611169 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq314 (M.op x x) (M.op x x)
       have i₂ := eq593808
       grind)
    | exact superpose eq593808 eq314
    | (have j0 := eq314 (M.op x x) (M.op x x)
       grind)
    | exact resolve eq314 eq593808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq593808
  have eq611180 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
  clear eq611169
  have eq673859 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq611180
       have i₂ := eq596245
       grind)
    | exact superpose eq596245 eq611180
    | exact resolve eq611180 eq596245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596245
  have eq673862 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq597598 X0 (σ (M.op x x))
       have i₂ := eq611180
       grind)
    | exact superpose eq611180 eq597598
    | exact resolve eq597598 eq611180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673881 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (M.op x x)) (M.op (σ (M.op x x)) X1))) = (M.op X0 (M.op (σ (M.op x x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2930 (σ (M.op x x)) X0 (σ (M.op x x)) X1
       have i₂ := eq611180
       grind)
    | exact superpose eq611180 eq2930
    | exact resolve eq2930 eq611180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930
  have eq673927 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x x)) X0) X1) = (M.op (σ (M.op x x)) (M.op X0 (M.op (σ (M.op x x)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38255 X1 (σ (M.op x x)) (σ (M.op x x)) X0
       have i₂ := eq611180
       grind)
    | exact superpose eq611180 eq38255
    | exact resolve eq38255 eq611180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38255
  have eq674097 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (σ (M.op x x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq673881 X0 X1
       have i₂ := eq3292 X0 X1 (σ (M.op x x))
       grind)
    | exact superpose eq3292 eq673881
    | exact resolve eq673881 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3292 eq673881
  have eq674120 : (σ (M.op x x)) = (M.op (σ (M.op x x)) y) := by
    first
    | (have i₁ := eq611180
       have i₂ := eq673862 (σ (M.op x x))
       grind)
    | exact superpose eq673862 eq611180
    | exact resolve eq611180 eq673862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611180
  have eq674206 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x x)) X0) X1) = (M.op (σ (M.op x x)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq673927 X0 X1
       have i₂ := eq674097 X0 X1
       grind)
    | exact superpose eq674097 eq673927
    | exact resolve eq673927 eq674097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673927 eq674097
  have eq674555 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq673859 eq597598
    | exact resolve eq597598 eq673859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674560 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq673859 eq12
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq673859
       grind)
    | exact resolve eq12 eq673859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674689 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq674560
  have eq675044 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq674689 eq180
    | exact resolve eq180 eq674689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq674689
  have eq680201 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq674555 eq673859
    | exact resolve eq673859 eq674555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673859 eq674555
  have eq680209 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq680201
  have eq680866 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op y (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq680209 eq595224
    | exact resolve eq595224 eq680209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595224 eq680209
  have eq681089 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq680866
       have i₂ := eq601303 sF4 sF3
       grind)
    | exact superpose eq601303 eq680866
    | exact resolve eq680866 eq601303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601303 eq680866
  have eq699594 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq675044 eq14
    | (have j0 := eq14 (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq14 eq675044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675044
  have eq699614 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq699594
  have eq700478 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq699614 eq597598
    | exact resolve eq597598 eq699614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597598
  have eq702180 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq700478 eq699614
    | exact resolve eq699614 eq700478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700478
  have eq702205 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq702180
  have eq702526 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (k y (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq702205 eq12
    | (have j0 := eq12 y (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq12 y (τ (M.op (σ x) (σ y)))
       have r₂ := eq702205
       grind)
    | exact resolve eq12 eq702205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702205
  have eq702661 : (k y (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq702526
  have eq841642 : (k (σ y) (M.op (σ x) (σ y))) = (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq702661 eq48
    | exact resolve eq48 eq702661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq702661
  have eq841675 : (k (σ y) (M.op (σ x) (σ y))) = (σ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq841642
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq841642
    | exact resolve eq841642 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq841642
  have eq857866 : (k (σ y) (M.op (σ x) (σ y))) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq699614 eq841675
    | exact resolve eq841675 eq699614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699614 eq841675
  have eq857886 : (k (σ y) (M.op (σ x) (σ y))) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq857866
  have eq857894 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq857886
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq857886
    | exact resolve eq857886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857886
  have eq857908 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq857894 eq14
    | (have j0 := eq14 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq14 eq857894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857910 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq857908
  have eq873177 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq857910 eq681089
    | exact resolve eq681089 eq857910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681089 eq857910
  have eq873263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq873177
  have eq873303 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq873263
       have r₂ := eq27
       grind)
    | exact resolve eq873263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873263
  have eq873398 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq873303 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq873303
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq873303
       grind)
    | exact resolve eq13 eq873303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873303
  have eq873507 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq873398
  have eq873508 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq873507
  have eq873688 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq873508 eq857894
    | exact resolve eq857894 eq873508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857894 eq873508
  have eq873699 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq873688
  have eq873711 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq873699 eq27
    | exact resolve eq27 eq873699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq873738 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq873699 eq595210
    | exact resolve eq595210 eq873699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595210
  have eq873761 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | exact superpose eq873699 eq596246
    | (have r₁ := eq596246
       have r₂ := eq873699
       grind)
    | exact resolve eq596246 eq873699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596246 eq873699
  have eq874756 : (σ y) = (σ (M.op x x)) := by grind
  clear eq873761
  have eq875411 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq673862 X0
       have i₂ := eq874756
       grind)
    | exact superpose eq874756 eq673862
    | exact resolve eq673862 eq874756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673862
  have eq875415 : (σ y) = (M.op (σ y) y) := by
    first
    | (have i₁ := eq674120
       have i₂ := eq874756
       grind)
    | exact superpose eq874756 eq674120
    | exact resolve eq674120 eq874756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674120
  have eq875419 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq674206 X0 X1
       have i₂ := eq874756
       grind)
    | exact superpose eq874756 eq674206
    | exact resolve eq674206 eq874756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674206 eq874756
  have eq876343 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op X0 (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq875419 eq873738
    | exact resolve eq873738 eq875419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873738 eq875419
  have eq877479 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq876343 x
       have i₂ := eq1983 sF3 x sF3
       grind)
    | exact superpose eq1983 eq876343
    | exact resolve eq876343 eq1983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983 eq876343
  have eq878537 : (σ (M.op x y)) = (M.op (σ y) y) := by
    first
    | exact superpose eq875411 eq877479
    | exact resolve eq877479 eq875411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875411 eq877479
  have eq879370 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq875415 eq878537
    | exact resolve eq878537 eq875415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875415 eq878537
  have eq879887 : False := by grind
  exact eq879887

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pyx_pxy_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq23
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
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
  have eq69 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X5 (M.op X0 (M.op X4 X2)))) X5) = (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 X3 X4 (M.op X0 (M.op X4 X2)) X5
       have i₂ := eq62 X0 X1 X2 X4
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq62 X0 x X2 X1
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq62 (M.op X0 X1) X2 X1 x
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq79 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) X2 X3
       have i₂ := eq79 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq79 eq79
    | exact resolve eq79 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (M.op X0 (M.op (M.op X1 X2) X1)) X1 X2
       have i₂ := eq79 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq79 eq79
    | exact resolve eq79 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op (M.op X3 X0) (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X0 X1 X2 X3 X4 x
       have i₂ := eq92 X3 x X0 (M.op X4 X2)
       grind)
    | exact superpose eq92 eq69
    | exact resolve eq69 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq92
  have eq126 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 X2 x
       have i₂ := eq114 X0 x X2 (M.op X1 X2) X0
       grind)
    | exact superpose eq114 eq63
    | exact resolve eq63 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq114
  have eq133 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X2 (M.op X0 X1) (M.op X2 X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq126
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X1 (M.op X0 (M.op X2 X1)) X2
       have i₂ := eq79 X0 X2 X1
       grind)
    | exact superpose eq79 eq126
    | exact resolve eq126 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (M.op (M.op X0 X2) X1) X1 X2
       have i₂ := eq126 X1 X0 X2
       grind)
    | exact superpose eq126 eq79
    | exact resolve eq79 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op X3 X4) X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X1 X2 (M.op X3 X4) (M.op (M.op X0 X4) X3)
       have i₂ := eq126 X3 X0 X4
       grind)
    | exact superpose eq126 eq62
    | exact resolve eq62 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq153 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X4) X3)) = (M.op (M.op X1 X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq151 X0 X1 x X3 X4
       have i₂ := eq91 X1 x X3 X4
       grind)
    | exact superpose eq91 eq151
    | exact resolve eq151 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq151
  have eq880 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 X2) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq145 (M.op X0 X2) X3 X1
       have i₂ := eq145 X0 X2 X1
       grind)
    | (have i₁ := eq145 (M.op X0 X2) X3 X1
       have i₂ := eq145 X0 X1 X2
       grind)
    | exact superpose eq145 eq145
    | exact resolve eq145 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq134 X3 (M.op X0 X2) X1
       have i₂ := eq145 X0 X2 X1
       grind)
    | (have i₁ := eq134 X3 (M.op X0 X2) X1
       have i₂ := eq145 X0 X1 X2
       grind)
    | exact superpose eq145 eq134
    | exact resolve eq134 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq966 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X2 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X0 X1 X2
       have i₂ := eq947 X1 X2 X1 X0
       grind)
    | exact superpose eq947 eq95
    | exact resolve eq95 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq982 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X3) X4) = (M.op (M.op X1 X0) (M.op X4 (M.op X0 X3))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq153 X0 X1 X3 X4
       have i₂ := eq947 X0 X4 X3 (M.op X1 X0)
       grind)
    | exact superpose eq947 eq153
    | exact resolve eq153 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq947
  have eq1141 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X0 X1 (M.op X2 X2)
       have i₂ := eq966 X0 X2 X1
       grind)
    | exact superpose eq966 eq79
    | exact resolve eq79 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1143 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133 X1 (M.op X0 X0) X2
       have i₂ := eq966 X2 X0 X2
       grind)
    | exact superpose eq966 eq133
    | exact resolve eq133 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq1165 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X2 X0 (M.op X1 X1)
       have i₂ := eq966 (M.op (M.op X0 (M.op X1 X1)) X2) X1 X2
       grind)
    | exact superpose eq966 eq126
    | exact resolve eq126 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1166 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X0 X1 (M.op X2 X2)
       have i₂ := eq966 (M.op (M.op X0 X1) (M.op X2 X2)) X2 X1
       grind)
    | exact superpose eq966 eq83
    | exact resolve eq83 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2383 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq2402 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) X1) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    grind
  have eq2429 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2383 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2437 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X0) (M.op X1 (M.op X0 X0))) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2402 X0 X1
       have i₂ := eq880 X0 X1 X0 (M.op X1 (M.op X0 X0))
       grind)
    | (have i₁ := eq2402 X1 x
       have i₂ := eq880 X1 X1 (M.op x (M.op X1 X1)) x
       grind)
    | exact superpose eq880 eq2402
    | (have j0 := eq2402 X0 X1
       grind)
    | exact resolve eq2402 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq2402
  have eq2446 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2429 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq2429 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2429 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2457 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X0) X1) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2437 X0 X1
       have i₂ := eq982 X0 (M.op X0 X1) X0 X1
       grind)
    | (have i₁ := eq2437 x X1
       have i₂ := eq982 X0 (M.op x X1) x (M.op X1 (M.op x x))
       grind)
    | exact superpose eq982 eq2437
    | (have j0 := eq2437 X0 X1
       grind)
    | exact resolve eq2437 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq2437
  have eq2534 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2446 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2535 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2446 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq2586 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2534 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq2534 X0 X1
       have i₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq2534
    | (have j0 := eq2534 X1 X0
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq2534 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq2534 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2588 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2534 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2534
  have eq2590 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2586 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586
  have eq2596 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2590 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq2590 (M.op (k X1 X1) (k X1 X1)) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | (have r₁ := eq2590 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2590 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2617 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2596 X0 X1
       have i₂ := eq2588 X1
       grind)
    | exact superpose eq2588 eq2596
    | (have j0 := eq2596 X0 X1
       grind)
    | exact resolve eq2596 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2596
  have eq2652 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2588 (σ X0)
       grind)
    | exact superpose eq2588 eq15
    | exact resolve eq15 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2654 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq2588 (τ X0)
       grind)
    | exact superpose eq2588 eq32
    | exact resolve eq32 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq2663 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2654 X0
       have i₂ := eq2588 X0
       grind)
    | exact superpose eq2588 eq2654
    | exact resolve eq2654 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654
  have eq2665 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2652 X0
       have i₂ := eq2588 X0
       grind)
    | exact superpose eq2588 eq2652
    | exact resolve eq2652 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588 eq2652
  have eq2720 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1143 X2 X1 (τ X0)
       have i₂ := eq2663 X0
       grind)
    | exact superpose eq2663 eq1143
    | exact resolve eq1143 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq2722 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (τ (M.op X0 X0))) X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1166 X1 X2 (τ X0)
       have i₂ := eq2663 X0
       grind)
    | exact superpose eq2663 eq1166
    | exact resolve eq1166 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq2756 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1141 (σ X0) (σ X0) X1
       have i₂ := eq2665 X0
       grind)
    | exact superpose eq2665 eq1141
    | exact resolve eq1141 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq2764 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq2665 X0
       grind)
    | exact superpose eq2665 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2766 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq966 X1 (σ X0) X2
       have i₂ := eq2665 X0
       grind)
    | exact superpose eq2665 eq966
    | exact resolve eq966 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq2775 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2764 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq2764 X0 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       have r₂ := eq12 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq2764 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq2764 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764
  have eq3404 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2720 (τ X0) X1 X2
       have i₂ := eq2663 X0
       grind)
    | exact superpose eq2663 eq2720
    | exact resolve eq2720 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq3966 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (τ (τ (M.op X0 X0)))) X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2722 (τ X0) X1 X2
       have i₂ := eq2663 X0
       grind)
    | exact superpose eq2663 eq2722
    | exact resolve eq2722 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722
  have eq4196 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (σ (M.op X2 X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq134 X0 X1 (σ (M.op X2 X2))
       have i₂ := eq2766 X2 X0 X1
       grind)
    | exact superpose eq2766 eq134
    | exact resolve eq134 eq2766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq2766
  have eq7888 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3404 (τ X0) X1 X2
       have i₂ := eq2663 X0
       grind)
    | exact superpose eq2663 eq3404
    | exact resolve eq3404 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404
  have eq8734 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (τ (τ (τ (M.op X0 X0))))) X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3966 (τ X0) X1 X2
       have i₂ := eq2663 X0
       grind)
    | exact superpose eq2663 eq3966
    | exact resolve eq3966 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663 eq3966
  have eq20959 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) ≠ (M.op X0 (τ (τ (τ (M.op X1 X1))))) ∨ (M.op (M.op X2 X2) X0) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2535 X0 (M.op X2 X2)
       have i₂ := eq7888 X1 X0 X2
       grind)
    | exact superpose eq7888 eq2535
    | (have j0 := eq2535 X0 (M.op X2 X2)
       grind)
    | exact resolve eq2535 eq7888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535 eq7888
  have eq28000 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X0 (τ (τ (τ (M.op X1 X1))))) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8734 X1 (M.op X0 (τ (τ (τ (M.op X1 X1))))) X0
       have i₂ := eq2457 X0 (τ (τ (τ (M.op X1 X1))))
       grind)
    | exact superpose eq2457 eq8734
    | (have j1 := eq2457 X0 X1
       grind)
    | exact resolve eq8734 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457 eq8734
  have eq28149 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq28000 X0 x
       have j1 := eq20959 X0 x X0
       grind)
    | (have r₁ := eq28000 X0 x
       have r₂ := eq20959 X0 x X0
       grind)
    | exact resolve eq28000 eq20959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20959 eq28000
  have eq28612 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq28149 (σ X0)
       have i₂ := eq2665 X0
       grind)
    | exact superpose eq2665 eq28149
    | exact resolve eq28149 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq28629 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq28612 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq28612
    | exact resolve eq28612 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28612
  have eq28677 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq28629 X0
       have i₂ := eq28149 X0
       grind)
    | exact superpose eq28149 eq28629
    | exact resolve eq28629 eq28149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28149 eq28629
  have eq28722 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2756 X0 X1
       have i₂ := eq28677 X0
       grind)
    | exact superpose eq28677 eq2756
    | exact resolve eq2756 eq28677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2756 eq28677
  have eq29346 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28722 (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq1165 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq1165 eq28722
    | exact resolve eq28722 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165 eq28722
  have eq32692 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29346 X0 X1 x
       have i₂ := eq29346 X0 X2 x
       grind)
    | exact superpose eq29346 eq29346
    | exact resolve eq29346 eq29346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32787 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ X0) (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4196 (σ X0) (σ (M.op X2 X2)) X2
       have i₂ := eq29346 X0 X1 (σ (M.op X2 X2))
       grind)
    | exact superpose eq29346 eq4196
    | exact resolve eq4196 eq29346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196 eq29346
  have eq315142 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq2775 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq2775 X0 (σ X0)
       grind)
    | exact superpose eq2775 eq10
    | (have j1 := eq2775 X1 X0
       grind)
    | exact resolve eq10 eq2775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq352944 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq315142 (σ X1) X0
       grind)
    | exact superpose eq315142 eq15
    | (have j1 := eq315142 (σ X1) X0
       grind)
    | exact resolve eq15 eq315142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315142
  have eq352977 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq352944 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq352944
    | (have j0 := eq352944 X0 X1
       grind)
    | exact resolve eq352944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352944
  have eq488097 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq352977 x y
       grind)
    | exact superpose eq352977 eq16
    | (have j1 := eq352977 x y
       grind)
    | exact resolve eq16 eq352977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352977
  have eq489720 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq488097
       have i₂ := eq2617 y x
       grind)
    | exact superpose eq2617 eq488097
    | (have j1 := eq2617 y x
       grind)
    | exact resolve eq488097 eq2617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617 eq488097
  have eq489724 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq489720
  have eq489725 : y = (M.op x x) := by grind
  clear eq489724
  have eq489862 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq32692 X0 X1 x
       have i₂ := eq489725
       grind)
    | exact superpose eq489725 eq32692
    | exact resolve eq32692 eq489725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32692
  have eq489865 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ X0) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq32787 X0 X1 x
       have i₂ := eq489725
       grind)
    | exact superpose eq489725 eq32787
    | exact resolve eq32787 eq489725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32787 eq489725
  have eq499575 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq489865 X0 x
       have i₂ := eq489862 X0 x
       grind)
    | exact superpose eq489862 eq489865
    | exact resolve eq489865 eq489862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489862 eq489865
  have eq512395 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq499575 x
       grind)
    | exact superpose eq499575 eq16
    | (have r₁ := eq16
       have r₂ := eq499575 x
       grind)
    | exact resolve eq16 eq499575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499575
  have eq512396 : False := by grind
  exact eq512396

/-- `Equation2688`: `x = ((x ◇ y) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_pxx_pyx_Equation2688 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2688 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2688.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
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
  clear eq36
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
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X0 (M.op X3 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X2 X2)) X1 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X2
       have i₂ := eq16 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) ≠ X0 ∨ (k (M.op (M.op X0 X1) (M.op X2 X2)) X1) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq570 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X2 X2)) X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X1 X0 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq570
       grind)
    | exact superpose eq570 eq40
    | exact resolve eq40 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq597 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq596
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq596
    | exact resolve eq596 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq599 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq597
    | exact resolve eq597 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq599 eq571
    | exact resolve eq571 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq607
       have r₂ := eq27
       grind)
    | exact resolve eq607 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq619 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq614 eq176
    | exact resolve eq176 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq614 eq27
    | exact resolve eq27 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op (M.op X0 X0) (M.op X1 X1))) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq619 (M.op X0 X0)
       have i₂ := eq178 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq619 (M.op X0 X0)
       have i₂ := eq178 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq178 eq619
    | exact resolve eq619 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X1 X1)) (σ y)) = (M.op (σ y) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq619 eq16
    | exact resolve eq16 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq641 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op (σ y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2))) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq622 (M.op X0 X0) X2
       have i₂ := eq178 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq622 (M.op X0 X0) X2
       have i₂ := eq178 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq178 eq622
    | exact resolve eq622 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq713 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ (k y x) = (M.op y y) := by
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
  have eq714 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1826 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq641 x x (M.op x x)
       have i₂ := eq177 sF3 sF3 x (M.op (M.op x x) (M.op x x))
       grind)
    | exact superpose eq177 eq641
    | exact resolve eq641 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq1925 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1826 eq1826
    | exact resolve eq1826 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1951 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ x)) X1) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1826 eq16
    | exact resolve eq16 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1954 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 (M.op X2 X2)) X1) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1826 eq177
    | exact resolve eq177 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1957 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1826 eq178
    | exact resolve eq178 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1965 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1826 eq630
    | exact resolve eq630 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq1826
  have eq2042 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1965 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1965
  have eq2059 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1925
  have eq2066 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 (σ x)) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1957 eq1954
    | exact resolve eq1954 eq1957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq2291 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = (M.op X1 (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1957 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq1957
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq1957 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3133 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) X1) X1) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2066 eq1951
    | exact resolve eq1951 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3144 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (σ x)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2066 eq1951
    | exact resolve eq1951 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066
  have eq3153 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq3144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3144
  have eq3156 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) X1) X1) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq3133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3133
  have eq3343 : x = (M.op (M.op (M.op x y) y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3153 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3153
    | (have j0 := eq3153 x y
       grind)
    | exact resolve eq3153 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq3558 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3343 eq3156
    | exact resolve eq3156 eq3343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3633 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq3928 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq614 eq714
    | (have r₁ := eq714
       have r₂ := eq614
       grind)
    | exact resolve eq714 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq3929 : (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3928
  have eq3930 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq599 eq3929
    | exact resolve eq3929 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3929
  have eq3939 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3930 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3930
       grind)
    | exact resolve eq13 eq3930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3930
  have eq3948 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3939
  have eq3960 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3948
    | exact resolve eq3948 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948
  have eq3966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq599 eq3960
    | exact resolve eq3960 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3960
  have eq3968 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3966
       have r₂ := eq27
       grind)
    | exact resolve eq3966 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966
  have eq3971 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3968 eq2059
    | exact resolve eq2059 eq3968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq4024 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3968 eq1957
    | exact resolve eq1957 eq3968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq4031 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3968 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq3968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq4042 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024
  have eq4087 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3971
  have eq4091 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4031
       have r₂ := eq620
       grind)
    | exact resolve eq4031 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq4031
  have eq4185 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4091 eq116
    | exact resolve eq116 eq4091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq4091
  have eq4217 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq4185
    | exact resolve eq4185 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4185
  have eq4274 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq573 y y X0
       have i₂ := eq4217
       grind)
    | exact superpose eq4217 eq573
    | (have j0 := eq573 y (M.op (M.op x y) (M.op X0 X0)) x
       grind)
    | exact resolve eq573 eq4217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4341 : y = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq175 eq4274
    | exact resolve eq4274 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq4756 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4042 eq3156
    | exact resolve eq3156 eq4042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq4766 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756
  have eq5240 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq4341
       grind)
    | exact superpose eq4341 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq4341
       grind)
    | exact resolve eq13 eq4341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq5249 : y = (k y y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq5240
  have eq5301 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq4217 eq5249
    | exact resolve eq5249 eq4217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217 eq5249
  have eq5302 : y = (M.op x y) ∨ x = y := by grind
  clear eq5301
  have eq6546 : x = (M.op (M.op (M.op x y) y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4766 x
       have i₂ := eq3633 sF2
       grind)
    | exact superpose eq3633 eq4766
    | exact resolve eq4766 eq3633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633 eq4766
  have eq6573 : x = (M.op (M.op (M.op x y) y) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq6546
  have eq6604 : x = (M.op (M.op (M.op x y) x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5302 eq6573
    | exact resolve eq6573 eq5302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5302 eq6573
  have eq6630 : x = (M.op (M.op (M.op x y) x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6604 eq4042
    | exact resolve eq4042 eq6604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4042 eq6604
  have eq6644 : x = (M.op (M.op (M.op x y) x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq6630
  have eq6660 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6644 eq1951
    | exact resolve eq1951 eq6644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq6644
  have eq6682 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq6660
  have eq6754 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq6682
       grind)
    | exact superpose eq6682 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq6682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6756 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq6682
       grind)
    | exact superpose eq6682 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq6682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6682
  have eq6819 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6754
       have r₂ := eq6756
       grind)
    | exact resolve eq6754 eq6756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6754 eq6756
  have eq6929 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6819
       grind)
    | exact superpose eq6819 eq40
    | exact resolve eq40 eq6819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6819
  have eq6959 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6929
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6929
    | exact resolve eq6929 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6929
  have eq6964 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq6959
    | exact resolve eq6959 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6959
  have eq6981 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op X0 X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6964 eq573
    | (have j0 := eq573 (σ x) (M.op (σ (M.op x y)) (M.op X0 X0)) x
       grind)
    | exact resolve eq573 eq6964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6964
  have eq6992 : (σ x) = (M.op (M.op (σ (M.op x y)) (k (σ x) (σ x))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq575 eq6981
    | (have j1 := eq575 (σ x) x x
       grind)
    | exact resolve eq6981 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq6981
  have eq7005 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2291 eq6992
    | (have j1 := eq2291 (σ x) x
       grind)
    | exact resolve eq6992 eq2291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291 eq6992
  have eq7008 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4087 eq7005
    | exact resolve eq7005 eq4087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4087 eq7005
  have eq7009 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq7008
  have eq7079 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7009 eq2042
    | exact resolve eq2042 eq7009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042 eq7009
  have eq7101 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq7079
  have eq7167 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq7101
    | exact resolve eq7101 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7101
  have eq7185 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq614 eq7167
    | exact resolve eq7167 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq7167
  have eq7439 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7185 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq7185
       grind)
    | exact resolve eq13 eq7185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7185
  have eq7449 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq7439
  have eq7466 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq7449
    | exact resolve eq7449 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449
  have eq7473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq599 eq7466
    | exact resolve eq7466 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq7466
  have eq7478 : y = (M.op x y) := by
    first
    | (have r₁ := eq7473
       have r₂ := eq27
       grind)
    | exact resolve eq7473 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7473
  have eq7481 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7478
       grind)
    | exact superpose eq7478 eq18
    | exact resolve eq18 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7482 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq7478
       grind)
    | exact superpose eq7478 eq24
    | exact resolve eq24 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq7484 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq7478
       grind)
    | exact superpose eq7478 eq41
    | exact resolve eq41 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq7485 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq7478
       grind)
    | exact superpose eq7478 eq175
    | exact resolve eq175 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq7486 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq713
       have i₂ := eq7478
       grind)
    | exact superpose eq7478 eq713
    | (have r₁ := eq713
       have r₂ := eq7478
       grind)
    | exact resolve eq713 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq7487 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq7486
  have eq7489 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7482 eq20
    | exact resolve eq20 eq7482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7500 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq7482 eq366
    | exact resolve eq366 eq7482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq7482
  have eq8152 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq7485 eq177
    | exact resolve eq177 eq7485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7485
  have eq8221 : (k (M.op x y) (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq571 eq7500
    | exact resolve eq7500 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7500
  have eq8280 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq8221
    | exact resolve eq8221 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8221
  have eq8331 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq8152 eq16
    | exact resolve eq16 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8335 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X0 x) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq8152 eq177
    | exact resolve eq177 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq8337 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
    intro X0 X1
    first
    | exact superpose eq8152 eq178
    | exact resolve eq178 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq8152
  have eq8408 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8335 X0 X1 x
       have i₂ := eq8337 (M.op X0 X1) x
       grind)
    | exact superpose eq8337 eq8335
    | exact resolve eq8335 eq8337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8335
  have eq10650 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8331 X0 X1
       have i₂ := eq8408 (M.op X0 X1) X1
       grind)
    | (have i₁ := eq8331 X0 x
       have i₂ := eq8408 (M.op X0 x) x
       grind)
    | exact superpose eq8408 eq8331
    | exact resolve eq8331 eq8408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8331 eq8408
  have eq17804 : (M.op x y) ≠ (k (M.op x y) x) ∨ (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7487 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq7487
       grind)
    | exact resolve eq13 eq7487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17806 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7487 eq28
    | exact resolve eq28 eq7487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7487
  have eq17824 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq17804
       have r₂ := eq17806
       grind)
    | exact resolve eq17804 eq17806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17804 eq17806
  have eq17933 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq17824 eq8280
    | exact resolve eq8280 eq17824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17936 : (k (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq17824 eq40
    | exact resolve eq40 eq17824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17824
  have eq17944 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq42 eq17936
    | exact resolve eq17936 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq17936
  have eq17947 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7489 eq17944
    | exact resolve eq17944 eq7489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17944
  have eq17950 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq17947
    | exact resolve eq17947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17947
  have eq17953 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7489 eq17950
    | exact resolve eq17950 eq7489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17950
  have eq64298 : (k (σ (M.op x y)) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq17933 eq7484
    | exact resolve eq7484 eq17933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7484 eq17933
  have eq64329 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq64298
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq64298
    | exact resolve eq64298 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64298
  have eq64342 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq64329
    | exact resolve eq64329 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64329
  have eq64354 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7489 eq64342
    | exact resolve eq64342 eq7489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64342
  have eq64391 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq64354 eq573
    | (have j0 := eq573 (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) x
       grind)
    | exact resolve eq573 eq64354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq64354
  have eq64395 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq176 eq64391
    | exact resolve eq64391 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq64391
  have eq214438 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq64395 eq8337
    | exact resolve eq8337 eq64395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214462 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (M.op X0 X0)) ∨ (k (M.op (σ y) (M.op X0 X0)) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq64395 eq181
    | exact resolve eq181 eq64395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq214494 : (σ y) = (M.op (M.op (σ y) (σ y)) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq64395 eq10650
    | exact resolve eq10650 eq64395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10650
  have eq214594 : (σ y) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq64395 eq214494
    | exact resolve eq214494 eq64395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214494
  have eq214604 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) x) ∨ (k (M.op (σ y) (M.op X0 X0)) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq214462 x
       have i₂ := eq8337 sF3 x
       grind)
    | exact superpose eq8337 eq214462
    | (have j0 := eq214462 X0
       grind)
    | exact resolve eq214462 eq8337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214462
  have eq214654 : ∀ X0 : G, (k (M.op (σ y) (M.op X0 X0)) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq214604 X0
       grind)
    | (have r₁ := eq214604 X0
       have r₂ := eq214594
       grind)
    | exact resolve eq214604 eq214594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214604
  have eq214688 : (M.op (σ y) (M.op (σ y) x)) = (k (M.op (σ y) x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq214654 x
       have i₂ := eq8337 sF3 x
       grind)
    | exact superpose eq8337 eq214654
    | exact resolve eq214654 eq8337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214654
  have eq214706 : (M.op (σ y) (M.op (σ y) (σ y))) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq214438 eq214688
    | exact resolve eq214688 eq214438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214438 eq214688
  have eq214715 : (k (M.op (σ y) (σ y)) (σ y)) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq214706
       have i₂ := eq8337 sF3 sF3
       grind)
    | exact superpose eq8337 eq214706
    | exact resolve eq214706 eq8337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8337 eq214706
  have eq214718 : (k (σ y) (σ y)) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq64395 eq214715
    | exact resolve eq214715 eq64395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64395 eq214715
  have eq214722 : (k (σ y) (σ x)) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq17953 eq214718
    | exact resolve eq214718 eq17953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17953 eq214718
  have eq214725 : (M.op (σ x) (σ y)) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq571 eq214722
    | exact resolve eq214722 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214722
  have eq214726 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq214594 eq214725
    | exact resolve eq214725 eq214594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214594 eq214725
  have eq214727 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq214726
  have eq214814 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq214727 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq214727
       grind)
    | exact resolve eq13 eq214727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214727
  have eq214897 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq214814
  have eq214934 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7481 eq214897
    | exact resolve eq214897 eq7481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214897
  have eq215482 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq214934 eq8280
    | exact resolve eq8280 eq214934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8280 eq214934
  have eq215510 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq215482
  have eq215533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq215510 eq14
    | exact resolve eq14 eq215510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215510
  have eq215562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq215533
    | exact resolve eq215533 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215533
  have eq215567 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq215562
       have r₂ := eq27
       grind)
    | exact resolve eq215562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215562
  have eq215570 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq215567 eq27
    | exact resolve eq27 eq215567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215567
  have eq215661 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq215570
       have r₂ := eq7489
       grind)
    | exact resolve eq215570 eq7489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7489 eq215570
  have eq216517 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq215661 eq26
    | exact resolve eq26 eq215661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq216518 : y = (τ (σ x)) := by
    first
    | exact superpose eq215661 eq32
    | exact resolve eq32 eq215661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq216521 : ∀ X0 : G, (k y X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | exact superpose eq215661 eq48
    | exact resolve eq48 eq215661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq216524 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq215661 eq73
    | exact resolve eq73 eq215661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq216535 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq215661 eq571
    | exact resolve eq571 eq215661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq215661
  have eq216771 : ∀ X0 : G, (k X0 x) = (k X0 y) := by
    intro X0
    first
    | exact superpose eq60 eq216524
    | exact resolve eq216524 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq216524
  have eq216774 : ∀ X0 : G, (k x X0) = (k y X0) := by
    intro X0
    first
    | exact superpose eq45 eq216521
    | exact resolve eq216521 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq216521
  have eq216777 : x = y := by
    first
    | exact superpose eq30 eq216518
    | exact resolve eq216518 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq216518
  have eq216792 : ∀ X0 : G, (k X0 x) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq216771 X0
       have i₂ := eq7478
       grind)
    | exact superpose eq7478 eq216771
    | exact resolve eq216771 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216771
  have eq216793 : ∀ X0 : G, (k x X0) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq216774 X0
       have i₂ := eq7478
       grind)
    | exact superpose eq7478 eq216774
    | exact resolve eq216774 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216774
  have eq216794 : x = (M.op x y) := by
    first
    | (have i₁ := eq216777
       have i₂ := eq7478
       grind)
    | exact superpose eq7478 eq216777
    | exact resolve eq216777 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7478 eq216777
  have eq216842 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7481
       have i₂ := eq216794
       grind)
    | exact superpose eq216794 eq7481
    | exact resolve eq7481 eq216794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7481 eq216794
  have eq217718 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq216517 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq216517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216517
  have eq217824 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq217718
       have r₂ := eq216535
       grind)
    | exact resolve eq217718 eq216535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216535 eq217718
  have eq218279 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq216842 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq216842
       grind)
    | exact resolve eq13 eq216842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216842
  have eq218350 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq218279
  have eq218669 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq217824 eq98
    | exact resolve eq98 eq217824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq217824
  have eq218732 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq218669
       have i₂ := eq216793 x
       grind)
    | exact superpose eq216793 eq218669
    | exact resolve eq218669 eq216793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216793 eq218669
  have eq218749 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq218732
       have i₂ := eq216792 sF0
       grind)
    | exact superpose eq216792 eq218732
    | exact resolve eq218732 eq216792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216792 eq218732
  have eq218764 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq218350 eq218749
    | exact resolve eq218749 eq218350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218350 eq218749
  have eq218787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq218764 eq14
    | exact resolve eq14 eq218764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218764
  have eq218815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq218787
    | exact resolve eq218787 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq218787
  have eq218830 : False := by grind
  exact eq218830
