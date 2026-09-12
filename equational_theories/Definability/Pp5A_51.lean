import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxx_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq69 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) (M.op X3 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) = (M.op X3 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X4 (M.op (M.op X0 (M.op X2 X3)) (M.op (M.op X2 X3) X1)) X3 X2
       have i₂ := eq9 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq55 x X2 X0 X3
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq55 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq73 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq73 eq73
    | exact resolve eq73 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq73 X1 X0 X2
       grind)
    | exact superpose eq73 eq55
    | exact resolve eq55 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq91 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq113 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op (M.op X2 X1) (M.op (M.op X4 (M.op X2 X1)) (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 (M.op X1 (M.op X1 X0)) (M.op X2 X1) X4
       have i₂ := eq77 X1 X2 X0
       grind)
    | exact superpose eq77 eq55
    | exact resolve eq55 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X4 (M.op X1 (M.op X1 X0))) X3)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq55 (M.op x X1) X3 (M.op X1 (M.op X1 X0)) X4
       have i₂ := eq77 X1 x X0
       grind)
    | exact superpose eq77 eq55
    | exact resolve eq55 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq77
  have eq118 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) X3)) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq114 X0 X1 X3 x
       have i₂ := eq88 X3 X1 (M.op X1 X0) x
       grind)
    | exact superpose eq88 eq114
    | exact resolve eq114 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq119 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X1 (M.op X1 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq113 X0 X1 X2 X3 x
       have i₂ := eq88 (M.op X1 (M.op X1 X0)) X2 X1 x
       grind)
    | exact superpose eq88 eq113
    | exact resolve eq113 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq113
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq272 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq272
    | (have j0 := eq272 (σ X0)
       grind)
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
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
  have eq1187 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq2170 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq96 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X1))) X3 X5 X2
       have i₂ := eq119 X1 (M.op X2 X3) X0 X4
       grind)
    | exact superpose eq119 eq96
    | exact resolve eq96 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq119
  have eq2179 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X1)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2170 X0 X1 X2 X3 X4 X5
       have i₂ := eq118 X3 X2 (M.op (M.op X2 X3) X1)
       grind)
    | exact superpose eq118 eq2170
    | exact resolve eq2170 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq2170
  have eq2300 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X0 (M.op X2 X3))) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2179 X0 X1 X2 X3 X4 x
       have i₂ := eq69 X2 X1 X2 X3 x
       grind)
    | exact superpose eq69 eq2179
    | exact resolve eq2179 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2179
  have eq2449 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op X3 (M.op X4 (M.op X0 X0))) X2) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2300 X4 X2 X1 X1 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq2300 X0 X1 X0 X0 X4
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq2300
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq2300 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2612 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2449 X0 X1 X2 x x
       have i₂ := eq2300 x X2 X0 X0 x
       grind)
    | exact superpose eq2300 eq2449
    | (have j0 := eq2449 X0 X1 X2 x x
       grind)
    | exact resolve eq2449 eq2300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2300 eq2449
  have eq14269 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq1187
  have eq14314 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14269
  have eq15748 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2
    grind
  clear eq2612
  have eq15801 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq15748 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15748
  have eq16123 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X3 X0) (M.op X2 X1))) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 X3
       have i₂ := eq15801 X1 X2 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq15801 X0 X1 X2
       grind)
    | exact superpose eq15801 eq9
    | (have j1 := eq15801 X0 X2 X0
       grind)
    | exact resolve eq9 eq15801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15801
  have eq22687 : ∀ X0 X2 : G, X0 = X2 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq1162 X2 X0 x
       have i₂ := eq16123 X0 X2 X2 x
       grind)
    | exact superpose eq16123 eq1162
    | (have j0 := eq1162 X2 X0 X2
       have j1 := eq16123 X0 x X2 x
       grind)
    | exact resolve eq1162 eq16123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq16123
  have eq22743 : ∀ X0 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X2 ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have j0 := eq22687 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22687
  have eq22866 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq22743
  have eq23049 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq22866 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22866
  have eq23065 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23049 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq23049
    | (have j0 := eq23049 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq23049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23076 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq23049 X0 (τ X1)
       grind)
    | exact superpose eq23049 eq19
    | (have j1 := eq23049 (k (σ X0) X1) (σ (M.op (τ X1) X0))
       grind)
    | exact resolve eq19 eq23049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23049
  have eq23505 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23076 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23076
    | exact resolve eq23076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23076
  have eq23596 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23505 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq23505
    | (have j0 := eq23505 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq23505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23505
  have eq23887 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23065 y x
       grind)
    | exact superpose eq23065 eq16
    | (have j1 := eq23065 x y
       grind)
    | exact resolve eq16 eq23065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23065
  have eq23999 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23887
       have i₂ := eq23596 x y
       grind)
    | exact superpose eq23596 eq23887
    | (have j1 := eq23596 (σ x) (σ y)
       grind)
    | (have r₁ := eq23887
       have r₂ := eq23596 x y
       grind)
    | (have r₁ := eq23887
       have r₂ := eq23596 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq23887
       have r₂ := eq23596 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq23887 eq23596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23596 eq23887
  have eq24002 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq23999
  have eq24010 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24002
       grind)
    | exact superpose eq24002 eq10
    | exact resolve eq10 eq24002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24002
  have eq24054 : x = y ∨ x = y := by
    first
    | (have i₁ := eq24010
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24010
    | exact resolve eq24010 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24010
  have eq24055 : x = y := by grind
  clear eq24054
  have eq24057 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24055
       grind)
    | exact superpose eq24055 eq16
    | exact resolve eq16 eq24055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24055
  have eq24058 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24057
       have i₂ := eq273 x
       grind)
    | exact superpose eq273 eq24057
    | (have j1 := eq273 x
       grind)
    | exact resolve eq24057 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq26757 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24058
       have i₂ := eq272 x
       grind)
    | exact superpose eq272 eq24058
    | (have j1 := eq272 (σ x)
       grind)
    | exact resolve eq24058 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26758 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq26757
  have eq26770 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq26758
       grind)
    | exact superpose eq26758 eq57
    | exact resolve eq57 eq26758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq26883 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26770
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26770
    | exact resolve eq26770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26770
  have eq27529 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26883
       have i₂ := eq26758
       grind)
    | exact superpose eq26758 eq26883
    | exact resolve eq26883 eq26758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26758 eq26883
  have eq27560 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq27529
  have eq27561 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq27560
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27560
    | exact resolve eq27560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27560
  have eq27567 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq272 x
       have i₂ := eq27561
       grind)
    | exact superpose eq27561 eq272
    | (have j0 := eq272 x
       grind)
    | exact resolve eq272 eq27561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq27561
  have eq27568 : x = (M.op x x) := by grind
  clear eq27567
  have eq27592 : ∀ X0 : G, (M.op X0 x) = (k x X0) ∨ (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq14314 x x
       have i₂ := eq27568
       grind)
    | exact superpose eq27568 eq14314
    | (have j0 := eq14314 x X0
       grind)
    | exact resolve eq14314 eq27568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14314
  have eq27662 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq27592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27592
  have eq27718 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24058
       have i₂ := eq27662 x
       grind)
    | exact superpose eq27662 eq24058
    | exact resolve eq24058 eq27662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24058 eq27662
  have eq27735 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq27718
  have eq27761 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24057
       have i₂ := eq27735
       grind)
    | exact superpose eq27735 eq24057
    | exact resolve eq24057 eq27735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24057 eq27735
  have eq27889 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq27761
       have i₂ := eq27568
       grind)
    | exact superpose eq27568 eq27761
    | exact resolve eq27761 eq27568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27568 eq27761
  have eq27890 : False := by grind
  exact eq27890

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq116 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X2 X0) X2 x X1
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq516 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq166
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq166
    | exact resolve eq166 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq516
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq516
    | (have j1 := eq56 y x
       grind)
    | exact resolve eq516 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq516
  have eq553 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq552
  have eq734 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq116
    | exact resolve eq116 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23552 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ y) (σ (M.op y y)))) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq116 (σ x) X0 (σ y)
       have i₂ := eq553
       grind)
    | exact superpose eq553 eq116
    | exact resolve eq116 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq23629 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq23552 x
       have i₂ := eq734 y x
       grind)
    | exact superpose eq734 eq23552
    | exact resolve eq23552 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq23552
  have eq23676 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq23629
       grind)
    | exact superpose eq23629 eq10
    | exact resolve eq10 eq23629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23629
  have eq23736 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq23676
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23676
    | exact resolve eq23676 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23676
  have eq24249 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23736
       grind)
    | exact superpose eq23736 eq16
    | exact resolve eq16 eq23736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23736
  have eq24250 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq24249
       have r₂ := eq95 x
       grind)
    | exact resolve eq24249 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24249
  have eq24316 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq116 y X0 y
       have i₂ := eq24250
       grind)
    | exact superpose eq24250 eq116
    | exact resolve eq116 eq24250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24250
  have eq24418 : x = y := by
    first
    | (have i₁ := eq24316 x
       have i₂ := eq116 x x y
       grind)
    | exact superpose eq116 eq24316
    | exact resolve eq24316 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq24316
  have eq24487 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24418
       grind)
    | exact superpose eq24418 eq16
    | exact resolve eq16 eq24418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24418
  have eq24489 : False := by grind
  exact eq24489

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pxy_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (k (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq77
    | exact resolve eq77 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq93
  have eq98 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq97
  have eq128 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq10
    | exact resolve eq10 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op (M.op x y) (M.op y X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 x
       have i₂ := eq58 X2 X0 X1 x
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : ∀ X0 : G, (M.op y (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq213 eq53
    | exact resolve eq53 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 X2 : G, (M.op (M.op X1 y) X0) = (M.op y (M.op (M.op X2 y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq874 eq58
    | exact resolve eq58 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq892 X0 X1 x
       have i₂ := eq14 (M.op sF0 X0) y x
       grind)
    | exact superpose eq14 eq892
    | exact resolve eq892 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq933 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq218 eq54
    | exact resolve eq54 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ y) (M.op (M.op X2 (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq933 eq58
    | exact resolve eq58 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq953 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq951 X0 X1 x
       have i₂ := eq14 (M.op sF4 X0) sF3 x
       grind)
    | exact superpose eq14 eq951
    | exact resolve eq951 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq3276 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq430 X0 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq430
    | exact resolve eq430 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq3296 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3276 X0
       have i₂ := eq45 (M.op X0 X0)
       grind)
    | exact superpose eq45 eq3276
    | exact resolve eq3276 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3276
  have eq9422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq9423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq9422
    | exact resolve eq9422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9422
  have eq9434 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq9423
       have r₂ := eq28
       grind)
    | exact resolve eq9423 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9423
  have eq9439 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq9434 eq54
    | exact resolve eq54 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq9448 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq9434 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq9434
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9434
       grind)
    | exact resolve eq12 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9434
  have eq9467 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq9448
  have eq9468 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq9467
  have eq9723 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq9468 eq62
    | exact resolve eq62 eq9468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq9468
  have eq9742 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq130 eq9723
    | exact resolve eq9723 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq9723
  have eq9743 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq9742
       have r₂ := eq12 x y
       grind)
    | exact resolve eq9742 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9742
  have eq9882 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq9743
       grind)
    | exact superpose eq9743 eq49
    | exact resolve eq49 eq9743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq9743
  have eq9899 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9882
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq9882
    | exact resolve eq9882 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9882
  have eq9903 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9899 eq60
    | exact resolve eq60 eq9899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq9899
  have eq11993 : (σ (k (M.op y y) (k x y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9903 (M.op y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq9903
    | exact resolve eq9903 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq12099 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (k x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11993
  have eq12108 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (k x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq953 eq12099
    | exact resolve eq12099 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq12099
  have eq12113 : (σ (k (M.op y y) (k x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq218 eq12108
    | exact resolve eq12108 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq12108
  have eq58377 : ∀ X0 : G, (σ (k X0 (k x y))) = (σ (k X0 (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9903 eq128
    | exact resolve eq128 eq9903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq9903
  have eq67990 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (σ (k (M.op y y) (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq58377 (M.op y y)
       have i₂ := eq12113
       grind)
    | exact superpose eq12113 eq58377
    | exact resolve eq58377 eq12113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12113 eq58377
  have eq68073 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) = (σ (k (M.op y y) (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq67990
  have eq68095 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq68073
  have eq68110 : (σ (M.op (M.op x y) (M.op y y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68095
       have i₂ := eq894 (M.op y y) y
       grind)
    | exact superpose eq894 eq68095
    | exact resolve eq68095 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq68095
  have eq68124 : (σ (M.op y (M.op (M.op x y) y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq213 eq68110
    | exact resolve eq68110 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq68110
  have eq68153 : (M.op y (M.op (M.op x y) y)) = (τ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq68124 eq16
    | exact resolve eq16 eq68124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68607 : (τ (σ x)) = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq9439 eq68153
    | exact resolve eq68153 eq9439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9439 eq68153
  have eq68645 : (τ (σ x)) = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq68607
  have eq68651 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq68645
    | exact resolve eq68645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68645
  have eq68659 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | exact superpose eq68651 eq874
    | exact resolve eq874 eq68651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq68651
  have eq68759 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq68659
  have eq68936 : x = (M.op y (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq68759
       grind)
    | exact superpose eq68759 eq53
    | exact resolve eq53 eq68759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq68984 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq669 x y X0
       have i₂ := eq68759
       grind)
    | exact superpose eq68759 eq669
    | exact resolve eq669 eq68759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69297 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq68936 eq68124
    | exact resolve eq68124 eq68936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68124 eq68936
  have eq69403 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq69297
  have eq69498 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq69403
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq69403
    | exact resolve eq69403 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69403
  have eq70153 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq69498 eq933
    | exact resolve eq933 eq69498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq69498
  have eq70678 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq70153 eq665
    | exact resolve eq665 eq70153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70680 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq70153 eq669
    | exact resolve eq669 eq70153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq72333 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68984 x
       have i₂ := eq68759
       grind)
    | exact superpose eq68759 eq68984
    | exact resolve eq68984 eq68759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68759 eq68984
  have eq72450 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq72333
  have eq72485 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq72450
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72450
    | exact resolve eq72450 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72450
  have eq72735 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq72485 eq665
    | exact resolve eq665 eq72485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq72485
  have eq82550 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq70153 eq70680
    | exact resolve eq70680 eq70153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70153 eq70680
  have eq82691 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq82550
  have eq82742 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq82691
    | exact resolve eq82691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82691
  have eq82779 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq82742 eq70678
    | exact resolve eq70678 eq82742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82742
  have eq82878 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq82779
  have eq102440 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3296 x
       have i₂ := eq72735 x
       grind)
    | exact superpose eq72735 eq3296
    | exact resolve eq3296 eq72735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296 eq72735
  have eq102612 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq102440
    | exact resolve eq102440 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102440
  have eq102642 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq102612
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq102612
    | exact resolve eq102612 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102612
  have eq102669 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq102642 eq70678
    | exact resolve eq70678 eq102642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70678 eq102642
  have eq102764 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq102669
  have eq102781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq102764 eq82878
    | exact resolve eq82878 eq102764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82878 eq102764
  have eq102896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq102781
  have eq102932 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq102896
       have r₂ := eq28
       grind)
    | exact resolve eq102896 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102896
  have eq102957 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq102932 eq30
    | exact resolve eq30 eq102932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq102932
  have eq103099 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq102957
    | exact resolve eq102957 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq102957
  have eq103100 : x = y := by grind
  clear eq103099
  have eq103282 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq103100
       grind)
    | exact superpose eq103100 eq19
    | exact resolve eq19 eq103100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq103283 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq103100
       grind)
    | exact superpose eq103100 eq25
    | exact resolve eq25 eq103100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq103100
  have eq103423 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq103283
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq103283
    | exact resolve eq103283 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq103283
  have eq103442 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq103423 eq27
    | exact resolve eq27 eq103423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq103423
  have eq103818 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq103442 eq70
    | exact resolve eq70 eq103442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq103442
  have eq103995 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq103818
       have i₂ := eq103282
       grind)
    | exact superpose eq103282 eq103818
    | exact resolve eq103818 eq103282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103282 eq103818
  have eq104019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103995 eq15
    | exact resolve eq15 eq103995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103995
  have eq104095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq104019
    | exact resolve eq104019 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq104019
  have eq104116 : False := by grind
  exact eq104116
