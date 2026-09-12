import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (M.op X0 X0) X1
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq45
    | exact resolve eq45 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq43 (M.op X0 X0)
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq43
    | exact resolve eq43 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq9
    | exact resolve eq9 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq106 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 (M.op X0 X0) X0 X1 X2
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq42
    | exact resolve eq42 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq42 X1 X4 X0 X2
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq16
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq252 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq49
    | exact resolve eq49 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq598 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq42 X1 X1 X0 X2
       grind)
    | exact superpose eq42 eq53
    | exact resolve eq53 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq739 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq598 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq43 (M.op X0 X1)
       grind)
    | exact superpose eq43 eq598
    | exact resolve eq598 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq739 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq739
    | exact resolve eq739 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq739 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq739
    | exact resolve eq739 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq839 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq783 X0 X1 X2
       have i₂ := eq784 (M.op X0 X2) X1
       grind)
    | exact superpose eq784 eq783
    | exact resolve eq783 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq1041 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq124 (M.op X0 X1) X0 X1 (M.op X0 X1) X2
       have i₂ := eq43 (M.op X0 X1)
       grind)
    | exact superpose eq43 eq124
    | exact resolve eq124 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq1122 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1041 X0 X1 X2
       have i₂ := eq784 X0 X2
       grind)
    | exact superpose eq784 eq1041
    | exact resolve eq1041 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1199 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op (M.op X1 X3) (M.op X2 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1122 (M.op X1 X3) (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq1122 X1 X3 X0
       grind)
    | exact superpose eq1122 eq1122
    | exact resolve eq1122 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1200 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 X0 (M.op X0 X0) X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq1122
    | exact resolve eq1122 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1249 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X0 X2 X1 X1
       have i₂ := eq1122 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq1122 eq42
    | exact resolve eq42 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq1269 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 (M.op x X0))
       have i₂ := eq1122 X0 (M.op x X0) x
       grind)
    | exact superpose eq1122 eq52
    | exact resolve eq52 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1282 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X1 X3) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X3) X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq1122 X1 X3 X0
       grind)
    | exact superpose eq1122 eq9
    | exact resolve eq9 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1299 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X2 (M.op X0 X1)) (M.op X3 (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1282 X0 X1 X2 X3
       have i₂ := eq784 X3 X1
       grind)
    | exact superpose eq784 eq1282
    | exact resolve eq1282 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1301 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1269 X0 X1
       have i₂ := eq839 X0 X1 X1
       grind)
    | exact superpose eq839 eq1269
    | exact resolve eq1269 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1332 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op (M.op X0 X1) (M.op X1 (M.op X2 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1199 X0 X1 X2 X3
       have i₂ := eq839 X1 X2 X3
       grind)
    | exact superpose eq839 eq1199
    | exact resolve eq1199 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1417 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq1200 X1 X0
       grind)
    | exact superpose eq1200 eq9
    | exact resolve eq9 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1428 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X0 X1) (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1122 X1 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq1200 X1 X0
       grind)
    | exact superpose eq1200 eq1122
    | exact resolve eq1122 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq598 X4 (M.op X1 (M.op X2 X0)) (M.op X0 X0) X3
       have i₂ := eq1417 X2 X0 X1
       grind)
    | exact superpose eq1417 eq598
    | exact resolve eq598 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq1715 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq739 (M.op X1 (M.op X2 X0)) (M.op X0 X0)
       have i₂ := eq1417 X2 X0 X1
       grind)
    | exact superpose eq1417 eq739
    | exact resolve eq739 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1724 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1715 X0 X1 X2
       have i₂ := eq784 (M.op X2 X0) X1
       grind)
    | exact superpose eq784 eq1715
    | exact resolve eq1715 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq1725 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1713 X0 X1 X2 X3 X4
       have i₂ := eq784 (M.op X2 X0) X1
       grind)
    | exact superpose eq784 eq1713
    | exact resolve eq1713 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1713
  have eq1747 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1725 X0 X1 X2 X3 X4
       have i₂ := eq1724 X0 X1 X2
       grind)
    | exact superpose eq1724 eq1725
    | exact resolve eq1725 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724 eq1725
  have eq1885 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (M.op X1 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1249 (M.op X2 X0) (M.op X0 X1) X2
       have i₂ := eq1249 X0 X1 X2
       grind)
    | (have i₁ := eq1249 X1 (M.op X0 X1) X2
       have i₂ := eq1249 X0 X1 X2
       grind)
    | exact superpose eq1249 eq1249
    | exact resolve eq1249 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1953 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1301 X1 X2
       have i₂ := eq1249 X1 X2 X0
       grind)
    | (have i₁ := eq1301 X0 (M.op X2 X0)
       have i₂ := eq1249 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1249 eq1301
    | exact resolve eq1301 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1954 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1200 X2 X1
       have i₂ := eq1249 X1 X2 X0
       grind)
    | (have i₁ := eq1200 (M.op X2 X0) X0
       have i₂ := eq1249 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1249 eq1200
    | exact resolve eq1200 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1955 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1122 X2 X3 X1
       have i₂ := eq1249 X1 X2 X0
       grind)
    | (have i₁ := eq1122 (M.op X2 X0) X1 X0
       have i₂ := eq1249 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1249 eq1122
    | exact resolve eq1122 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq2016 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1885 X0 X1 X2 X3
       have i₂ := eq839 X1 (M.op X0 X1) X2
       grind)
    | exact superpose eq839 eq1885
    | exact resolve eq1885 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq2043 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X3 X2) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2016 X0 X1 X2 X3
       have i₂ := eq1953 X0 X1 X2
       grind)
    | exact superpose eq1953 eq2016
    | exact resolve eq2016 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953 eq2016
  have eq2193 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq75 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2247 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2193 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2193
    | (have j0 := eq2193 X0 X1
       grind)
    | exact resolve eq2193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2687 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X3 (M.op X1 X2)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1954 X0 (M.op X0 X1) (M.op X0 (M.op X2 X0))
       have i₂ := eq1122 X0 X1 X2
       grind)
    | exact superpose eq1122 eq1954
    | exact resolve eq1954 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq2801 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X3 (M.op X1 X2)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2687 X0 X1 X2 X3
       have i₂ := eq1747 X1 (M.op X3 (M.op X1 X2)) X0 X1 X0
       grind)
    | exact superpose eq1747 eq2687
    | exact resolve eq2687 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2687
  have eq3215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq174
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq174
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq174
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq174
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq174 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3216 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3215
  have eq3646 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106 X1 X1 (M.op X1 (M.op X2 X1))
       have i₂ := eq1428 X1 X1 X2
       grind)
    | exact superpose eq1428 eq106
    | exact resolve eq106 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq3784 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3646 X0 X1 X2
       have i₂ := eq1747 X1 X2 X0 X2 X0
       grind)
    | exact superpose eq1747 eq3646
    | exact resolve eq3646 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747 eq3646
  have eq8530 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1299 X3 X1 X2 (M.op X0 X1)
       have i₂ := eq1428 X0 X1 X0
       grind)
    | exact superpose eq1428 eq1299
    | exact resolve eq1299 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299 eq1428
  have eq14050 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op X4 (M.op (M.op X3 X0) (M.op X0 X1))) (M.op (M.op X5 (M.op X1 X2)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2043 X0 (M.op X2 X3) (M.op (M.op X0 X1) (M.op X1 X2)) X3
       have i₂ := eq1955 X0 X1 X2 X3
       grind)
    | exact superpose eq1955 eq2043
    | exact resolve eq2043 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955 eq2043
  have eq14298 : ∀ X0 X1 X2 X5 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X5 (M.op X1 X2)) (M.op X0 X1))) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq14050 X0 X1 X2 x x X5
       have i₂ := eq8530 (M.op X5 (M.op X1 X2)) (M.op X0 X1) x (M.op x X0)
       grind)
    | exact superpose eq8530 eq14050
    | exact resolve eq14050 eq8530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8530 eq14050
  have eq14439 : ∀ X0 X1 X2 X5 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X5 (M.op X1 X2)) (M.op X0 X1))) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq14298 X0 X1 X2 X5
       have i₂ := eq839 X0 (M.op X5 (M.op X1 X2)) X1
       grind)
    | exact superpose eq839 eq14298
    | exact resolve eq14298 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq14298
  have eq17837 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X1 X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3784 X0 X1 (M.op X2 (M.op X1 X3))
       have i₂ := eq2801 X0 X1 X3 X2
       grind)
    | exact superpose eq2801 eq3784
    | exact resolve eq3784 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801 eq3784
  have eq40292 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X1 X3)) (M.op X0 X1)) = (M.op (M.op X4 X0) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1332 X4 X0 (M.op X2 (M.op X1 X3)) X1
       have i₂ := eq14439 X0 X1 X3 X2
       grind)
    | exact superpose eq14439 eq1332
    | exact resolve eq1332 eq14439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq14439
  have eq40742 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3216
       grind)
    | exact superpose eq3216 eq16
    | exact resolve eq16 eq3216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216
  have eq40743 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq40742
       have r₂ := eq22 x
       grind)
    | exact resolve eq40742 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40742
  have eq127682 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40743
       grind)
    | exact superpose eq40743 eq10
    | exact resolve eq10 eq40743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40743
  have eq127802 : x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127682
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq127682
    | exact resolve eq127682 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127682
  have eq127806 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127802
       grind)
    | exact superpose eq127802 eq16
    | exact resolve eq16 eq127802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127802
  have eq127807 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq127806
       have r₂ := eq22 x
       grind)
    | exact resolve eq127806 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127806
  have eq128071 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq127807
       grind)
    | exact superpose eq127807 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq127807
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq127807
       grind)
    | exact resolve eq13 eq127807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127807
  have eq128229 : x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq128071
  have eq130437 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128229
       grind)
    | exact superpose eq128229 eq16
    | exact resolve eq16 eq128229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128229
  have eq130442 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq130437
       have r₂ := eq22 x
       grind)
    | exact resolve eq130437 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130437
  have eq130449 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181 x y
       have i₂ := eq130442
       grind)
    | exact superpose eq130442 eq181
    | (have j0 := eq181 x y
       grind)
    | exact resolve eq181 eq130442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq130442
  have eq130459 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq130449
  have eq130460 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq130459
  have eq131132 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq130460
       grind)
    | exact superpose eq130460 eq10
    | exact resolve eq10 eq130460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130460
  have eq131254 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq131132
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq131132
    | exact resolve eq131132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131132
  have eq131258 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131254
       grind)
    | exact superpose eq131254 eq16
    | exact resolve eq16 eq131254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131254
  have eq131265 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq131258
       have r₂ := eq22 x
       grind)
    | exact resolve eq131258 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131258
  have eq131951 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131265
       grind)
    | exact superpose eq131265 eq16
    | exact resolve eq16 eq131265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131952 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq72 x X0 (σ y)
       have i₂ := eq131265
       grind)
    | exact superpose eq131265 eq72
    | exact resolve eq72 eq131265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq131970 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq131265
       grind)
    | exact superpose eq131265 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq131265
       grind)
    | exact resolve eq13 eq131265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131989 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq739 (σ x) (σ y)
       have i₂ := eq131265
       grind)
    | exact superpose eq131265 eq739
    | exact resolve eq739 eq131265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131996 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1122 (σ y) x (σ x)
       have i₂ := eq131265
       grind)
    | exact superpose eq131265 eq1122
    | exact resolve eq1122 eq131265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq132094 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq17837 (σ x) (σ y) x x
       have i₂ := eq131265
       grind)
    | exact superpose eq131265 eq17837
    | exact resolve eq17837 eq131265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17837
  have eq132131 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq131970
  have eq132149 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op (M.op X0 (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq132094 X0 X1
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq132094
    | exact resolve eq132094 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132094
  have eq132184 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq131996 X0
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq131996
    | exact resolve eq131996 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131996
  have eq132189 : (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq131989
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq131989
    | exact resolve eq131989 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131989
  have eq132202 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132131
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq132131
    | exact resolve eq132131 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132131
  have eq134826 : (σ x) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq131952 (σ x)
       have i₂ := eq131265
       grind)
    | exact superpose eq131265 eq131952
    | exact resolve eq131952 eq131265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131952
  have eq135417 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq739 (σ y) (σ (M.op x x))
       have i₂ := eq134826
       grind)
    | exact superpose eq134826 eq739
    | exact resolve eq739 eq134826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq134826
  have eq135661 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq135417
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq135417
    | exact resolve eq135417 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq135417
  have eq135761 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq135661
       have i₂ := eq131265
       grind)
    | exact superpose eq131265 eq135661
    | exact resolve eq135661 eq131265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131265 eq135661
  have eq150564 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq132184 (σ x)
       have i₂ := eq132189
       grind)
    | exact superpose eq132189 eq132184
    | exact resolve eq132184 eq132189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132184 eq132189
  have eq151019 : (σ y) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq150564
       have i₂ := eq135761
       grind)
    | exact superpose eq135761 eq150564
    | exact resolve eq150564 eq135761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150564
  have eq151409 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) X1)) (σ y)) = (M.op (M.op X2 (σ (M.op x x))) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40292 (σ (M.op x x)) (σ y) X2 x x
       have i₂ := eq151019
       grind)
    | exact superpose eq151019 eq40292
    | exact resolve eq40292 eq151019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40292 eq151019
  have eq151438 : ∀ X2 : G, (σ (M.op y y)) = (M.op (M.op X2 (σ (M.op x x))) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq151409 x x X2
       have i₂ := eq132149 x x
       grind)
    | exact superpose eq132149 eq151409
    | exact resolve eq151409 eq132149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132149 eq151409
  have eq151536 : ∀ X2 : G, (σ y) = (M.op (M.op X2 (σ (M.op x x))) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq151438 X2
       have i₂ := eq135761
       grind)
    | exact superpose eq135761 eq151438
    | exact resolve eq151438 eq135761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151438
  have eq151873 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2247 x y
       have i₂ := eq132202
       grind)
    | exact superpose eq132202 eq2247
    | (have j0 := eq2247 x y
       grind)
    | exact resolve eq2247 eq132202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247 eq132202
  have eq152015 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq151873
       have r₂ := eq131951
       grind)
    | exact resolve eq151873 eq131951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151873
  have eq166354 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq131951
       have i₂ := eq152015
       grind)
    | exact superpose eq152015 eq131951
    | exact resolve eq131951 eq152015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166368 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq135761
       have i₂ := eq152015
       grind)
    | exact superpose eq152015 eq135761
    | exact resolve eq135761 eq152015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135761 eq152015
  have eq166392 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq166354
       have r₂ := eq166368
       grind)
    | exact resolve eq166354 eq166368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166354 eq166368
  have eq166776 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ (M.op x x))) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq151536 x
       have i₂ := eq166392
       grind)
    | exact superpose eq166392 eq151536
    | exact resolve eq151536 eq166392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151536
  have eq166778 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq166392
       grind)
    | exact superpose eq166392 eq10
    | exact resolve eq10 eq166392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166392
  have eq166941 : x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq166778
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq166778
    | exact resolve eq166778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166778
  have eq166943 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq166776 x
       have i₂ := eq252 x x
       grind)
    | exact superpose eq252 eq166776
    | exact resolve eq166776 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq166776
  have eq166977 : (σ x) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq131951
       have i₂ := eq166941
       grind)
    | exact superpose eq166941 eq131951
    | exact resolve eq131951 eq166941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166941
  have eq167015 : y = (M.op x y) := by
    first
    | (have r₁ := eq166977
       have r₂ := eq166943
       grind)
    | exact resolve eq166977 eq166943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166943 eq166977
  have eq167467 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq131951
       have i₂ := eq167015
       grind)
    | exact superpose eq167015 eq131951
    | exact resolve eq131951 eq167015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131951 eq167015
  have eq167636 : False := by grind
  exact eq167636

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
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
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq10
    | exact resolve eq10 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq138 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128 x y
       grind)
    | exact superpose eq128 eq16
    | (have j1 := eq128 x y
       grind)
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq154 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq26
    | exact resolve eq26 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq70
  have eq329 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq154 (M.op X0 X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq154
    | exact resolve eq154 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq154
  have eq363 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq329 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq329
    | exact resolve eq329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq373 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (M.op (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq363
    | exact resolve eq363 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq376 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq373 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq373
    | exact resolve eq373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq406 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq376 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq376
    | exact resolve eq376 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq138
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq138
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq138
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq138
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq138 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq747 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq746
  have eq13388 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq747
       grind)
    | exact superpose eq747 eq16
    | exact resolve eq16 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq13389 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq13388
       have r₂ := eq23 x
       grind)
    | exact resolve eq13388 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13388
  have eq128760 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13389
       grind)
    | exact superpose eq13389 eq10
    | exact resolve eq10 eq13389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13389
  have eq129024 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq128760
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq128760
    | exact resolve eq128760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128760
  have eq129027 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq129024
       grind)
    | exact superpose eq129024 eq16
    | exact resolve eq16 eq129024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129024
  have eq129028 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq129027
       have r₂ := eq23 x
       grind)
    | exact resolve eq129027 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq129027
  have eq129890 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq376 y
       have i₂ := eq129028
       grind)
    | exact superpose eq129028 eq376
    | exact resolve eq376 eq129028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129892 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq406 y
       have i₂ := eq129028
       grind)
    | exact superpose eq129028 eq406
    | exact resolve eq406 eq129028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129028
  have eq173876 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq129892
       grind)
    | exact superpose eq129892 eq16
    | exact resolve eq16 eq129892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129892
  have eq175155 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq173876
       have i₂ := eq129890
       grind)
    | exact superpose eq129890 eq173876
    | exact resolve eq173876 eq129890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129890 eq173876
  have eq175159 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq175155
  have eq175160 : (σ x) = (σ (M.op y y)) := by grind
  clear eq175159
  have eq175187 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq406 y
       have i₂ := eq175160
       grind)
    | exact superpose eq175160 eq406
    | exact resolve eq406 eq175160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq175248 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq175160
       grind)
    | exact superpose eq175160 eq10
    | exact resolve eq10 eq175160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175160
  have eq175673 : x = (M.op y y) := by
    first
    | (have i₁ := eq175248
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq175248
    | exact resolve eq175248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175248
  have eq176506 : x = (M.op x y) := by
    first
    | (have i₁ := eq376 y
       have i₂ := eq175673
       grind)
    | exact superpose eq175673 eq376
    | exact resolve eq376 eq175673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq175673
  have eq207526 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175187
       grind)
    | exact superpose eq175187 eq16
    | exact resolve eq16 eq175187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175187
  have eq207791 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq207526
       have i₂ := eq176506
       grind)
    | exact superpose eq176506 eq207526
    | exact resolve eq207526 eq176506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176506 eq207526
  have eq207792 : False := by grind
  exact eq207792

/-- `Equation1921`: `x = (y ◇ (y ◇ x)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1921 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1921 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1921.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  clear eq18
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq477 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq497 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq520 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq497 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq497
    | (have j0 := eq497 X0 X1
       grind)
    | exact resolve eq497 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq717 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
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
  have eq725 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq3295 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq494
    | exact resolve eq494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq3351 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3295 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3295
    | (have j0 := eq3295 X0 X1
       grind)
    | exact resolve eq3295 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295
  have eq7019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq717
       have i₂ := eq3351 y x
       grind)
    | exact superpose eq3351 eq717
    | (have j1 := eq3351 y x
       grind)
    | (have r₁ := eq717
       have r₂ := eq3351 y x
       grind)
    | (have r₁ := eq717
       have r₂ := eq3351 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq717
       have r₂ := eq3351 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq717 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq3351
  have eq7020 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7019
  have eq7032 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq725 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq725
    | (have j0 := eq725 (τ X0) (τ X1)
       grind)
    | exact resolve eq725 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq7099 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7032 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7032
    | (have j0 := eq7032 X0 X1
       grind)
    | exact resolve eq7032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7032
  have eq7134 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7099 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7099
    | (have j0 := eq7099 X0 X1
       grind)
    | exact resolve eq7099 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7099
  have eq7166 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7134 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7134
    | (have j0 := eq7134 X0 X1
       grind)
    | exact resolve eq7134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7134
  have eq7192 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7166 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7166
    | (have j0 := eq7166 X0 X1
       grind)
    | exact resolve eq7166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7166
  have eq7211 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7192 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7192
    | (have j0 := eq7192 X0 X1
       grind)
    | exact resolve eq7192 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7192
  have eq7228 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7211 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7211
    | (have j0 := eq7211 X0 X1
       grind)
    | exact resolve eq7211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7211
  have eq7241 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7228 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7228
    | (have j0 := eq7228 X0 X1
       grind)
    | exact resolve eq7228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7228
  have eq15113 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7020
       grind)
    | exact superpose eq7020 eq16
    | exact resolve eq16 eq7020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7020
  have eq15114 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15113
       have r₂ := eq22 x
       grind)
    | exact resolve eq15113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15113
  have eq15118 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15114
       grind)
    | exact superpose eq15114 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15114
       grind)
    | exact resolve eq13 eq15114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15114
  have eq15120 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15118
  have eq17075 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15120
       grind)
    | exact superpose eq15120 eq16
    | exact resolve eq16 eq15120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15120
  have eq17076 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq17075
       have r₂ := eq22 x
       grind)
    | exact resolve eq17075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17075
  have eq17079 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq477 x (σ y)
       have i₂ := eq17076
       grind)
    | exact superpose eq17076 eq477
    | (have j0 := eq477 x (σ y)
       grind)
    | (have r₁ := eq477 x (σ y)
       have r₂ := eq17076
       grind)
    | exact resolve eq477 eq17076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17076
  have eq17094 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq17079
  have eq17095 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq17094
  have eq17102 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17095
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17095
    | exact resolve eq17095 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17095
  have eq17115 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq725 x y
       have i₂ := eq17102
       grind)
    | exact superpose eq17102 eq725
    | (have j0 := eq725 x y
       grind)
    | (have r₁ := eq725 x y
       have r₂ := eq17102
       grind)
    | exact resolve eq725 eq17102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17102
  have eq17143 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq17115
  have eq17144 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq17143
  have eq17149 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq725 x y
       grind)
    | (have r₁ := eq17144
       have r₂ := eq725 x y
       grind)
    | exact resolve eq17144 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq17144
  have eq17152 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17149
       grind)
    | exact superpose eq17149 eq16
    | exact resolve eq16 eq17149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17153 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq477 x (σ y)
       have i₂ := eq17149
       grind)
    | exact superpose eq17149 eq477
    | (have j0 := eq477 x (σ y)
       grind)
    | (have r₁ := eq477 x (σ y)
       have r₂ := eq17149
       grind)
    | exact resolve eq477 eq17149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq17149
  have eq17168 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq17153
  have eq17169 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq17168
  have eq17176 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17169
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17169
    | exact resolve eq17169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17169
  have eq17187 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17176
       grind)
    | exact superpose eq17176 eq10
    | exact resolve eq10 eq17176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17176
  have eq17353 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17187
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17187
    | exact resolve eq17187 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17187
  have eq17355 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17353
       grind)
    | exact superpose eq17353 eq16
    | exact resolve eq16 eq17353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17353
  have eq17356 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq17355
       have r₂ := eq22 x
       grind)
    | exact resolve eq17355 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17355
  have eq17370 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq17356
       grind)
    | exact superpose eq17356 eq10
    | exact resolve eq10 eq17356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17356
  have eq17537 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq17370
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17370
    | exact resolve eq17370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17370
  have eq17567 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7241 x y
       have i₂ := eq17537
       grind)
    | exact superpose eq17537 eq7241
    | (have j0 := eq7241 x y
       grind)
    | (have r₁ := eq7241 x y
       have r₂ := eq17537
       grind)
    | exact resolve eq7241 eq17537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7241 eq17537
  have eq17570 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17567
  have eq17574 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17152
       have i₂ := eq17570
       grind)
    | exact superpose eq17570 eq17152
    | exact resolve eq17152 eq17570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17152 eq17570
  have eq17584 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17574
  have eq17585 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17584
       grind)
    | exact superpose eq17584 eq16
    | exact resolve eq16 eq17584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17584
  have eq17588 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17585
       have r₂ := eq22 x
       grind)
    | exact resolve eq17585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17585
  have eq17589 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17588
       grind)
    | exact superpose eq17588 eq16
    | exact resolve eq16 eq17588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17590 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17588
       grind)
    | exact superpose eq17588 eq10
    | exact resolve eq10 eq17588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17588
  have eq17756 : x = y := by
    first
    | (have i₁ := eq17590
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17590
    | exact resolve eq17590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17590
  have eq17757 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17589
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17589
    | exact resolve eq17589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17589
  have eq17758 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17757
       have i₂ := eq17756
       grind)
    | exact superpose eq17756 eq17757
    | exact resolve eq17757 eq17756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17756 eq17757
  have eq17759 : False := by grind
  exact eq17759

/-- `Equation1996`: `x = (y ◇ (z ◇ z)) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pxy_pyy_pxy_Equation1996 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1996 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1996.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X1 X0)) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X1)) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op X1 X1)) X0
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X3 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq76
    | (have j0 := eq76 (σ X0) (σ X1)
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op x x) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq99
  have eq107 : (M.op y x) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
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
    | (have r₁ := eq116 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
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
  have eq121 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq43
    | exact resolve eq43 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq122 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq117 y
       grind)
    | exact superpose eq117 eq74
    | exact resolve eq74 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq127 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq117 sF3
       grind)
    | exact superpose eq117 eq122
    | exact resolve eq122 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq128 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq121
    | exact resolve eq121 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq129 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq278 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
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
  have eq289 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq278 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq278
    | exact resolve eq278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq292 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq289 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq289
    | exact resolve eq289 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq289
  have eq527 : ∀ X0 : G, y = (M.op (M.op x (σ (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq52
    | exact resolve eq52 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq14
    | exact resolve eq14 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op (M.op X1 (M.op X3 X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X1 (M.op X3 X3)) X0) X1 X2
       have i₂ := eq51 X1 X3 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3)) ∨ (k X1 (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3))) = (M.op (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3)) (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 X3))
       have i₂ := eq54 X0 X1 X2 X3
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 X3)) X1
       have r₂ := eq54 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 X3)) X1 X2 X3
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 (M.op X2 X2)) (M.op X3 X3))
       have r₂ := eq54 X1 X1 X2 X3
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3)) ∨ (k X1 (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3))) = (M.op X1 (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3))
       have i₂ := eq54 X1 X0 X2 X3
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3))
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X3 X3) = (k X1 (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3))) ∨ (M.op X0 X1) = (M.op (M.op X0 (M.op X2 X2)) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq704 X0 X1 X2 X3
       have i₂ := eq14 (M.op X3 X3) (M.op X0 (M.op X2 X2)) X3
       grind)
    | exact superpose eq14 eq704
    | (have j0 := eq704 X0 X1 X2 X3
       grind)
    | exact resolve eq704 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq739 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq16
    | exact resolve eq16 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq811 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq825 : ∀ X0 : G, y = (M.op (M.op x (σ (σ (M.op X0 X0)))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq527 (σ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq527
    | exact resolve eq527 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq874 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq811 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq811
    | (have j0 := eq811 X0 y
       grind)
    | exact resolve eq811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq811
  have eq1003 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X1 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (τ X0)
       have i₂ := eq739 X0
       grind)
    | exact superpose eq739 eq14
    | exact resolve eq14 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (τ (M.op X0 X0))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (τ X0)
       have i₂ := eq739 X0
       grind)
    | exact superpose eq739 eq53
    | exact resolve eq53 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1054 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (τ (τ (M.op X0 X0)))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1006 (τ X0)
       have i₂ := eq739 X0
       grind)
    | exact superpose eq739 eq1006
    | exact resolve eq1006 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1006
  have eq1088 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x (σ (σ (M.op X0 X0)))) (M.op X1 X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq825 eq14
    | exact resolve eq14 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1141 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (τ (τ (M.op X0 X0)))) (M.op X1 X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1054 eq14
    | exact resolve eq14 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1363 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 X0)) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq14
    | exact resolve eq14 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq3554 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (σ (σ (M.op X0 X0)))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq529 (M.op x (σ (M.op X0 X0))) X1 X3
       have i₂ := eq529 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq529 eq529
    | exact resolve eq529 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq4715 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq874 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq874
    | (have j0 := eq874 x
       grind)
    | exact resolve eq874 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq874
  have eq4727 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4715
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4715
    | exact resolve eq4715 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4715
  have eq4748 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq4727
    | exact resolve eq4727 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727
  have eq4756 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4748
       have i₂ := eq128
       grind)
    | exact superpose eq128 eq4748
    | exact resolve eq4748 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq4748
  have eq4776 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq4756 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756
  have eq4779 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4776
    | exact resolve eq4776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4776
  have eq4780 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq4779
  have eq6895 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (τ (τ (M.op X0 X0)))) (M.op X1 X3)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1003 (M.op x (τ (M.op X0 X0))) X1 X3
       have i₂ := eq1003 X0 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq1003 eq1003
    | exact resolve eq1003 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq9965 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (σ X0) (M.op (M.op (σ X0) (M.op X2 X2)) (M.op X1 X1))) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (M.op X2 X2)) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq708 (σ X0) (σ X0) X2 x
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq708
    | (have j0 := eq708 (σ X0) (σ X0) X2 X1
       grind)
    | exact resolve eq708 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq9990 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (σ X0) (M.op (M.op (σ X0) (M.op X2 X2)) (M.op X1 X1))) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (M.op X2 X2)) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq9965 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9965
  have eq10431 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (M.op (M.op (σ X0) (M.op X1 X1)) (M.op X2 X2)) ∨ (k (σ X0) (M.op (M.op (σ X0) (M.op X1 X1)) (M.op X2 X2))) = (M.op (σ X0) (M.op (M.op (σ X0) (M.op X1 X1)) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq705 (σ X0) (σ X0) X1 X2
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq705
    | (have j0 := eq705 (σ X0) (σ X0) X1 X2
       grind)
    | exact resolve eq705 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq705
  have eq10485 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (σ X0) (M.op (M.op (σ X0) (M.op X1 X1)) (M.op X2 X2))) ∨ (σ (M.op X0 X0)) ≠ (M.op (M.op (σ X0) (M.op X1 X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10431 X0 X1 X2
       have i₂ := eq51 (σ X0) X1 (M.op X2 X2)
       grind)
    | exact superpose eq51 eq10431
    | (have j0 := eq10431 X0 X1 X2
       grind)
    | exact resolve eq10431 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq10431
  have eq53534 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54 X0 y x x
       have i₂ := eq1363 x
       grind)
    | exact superpose eq1363 eq54
    | exact resolve eq54 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq53667 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x (σ (σ (M.op X0 X0)))) (M.op x y)) y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1088 X0 y
       have i₂ := eq53534 y
       grind)
    | exact superpose eq53534 eq1088
    | exact resolve eq1088 eq53534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq53534
  have eq53898 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq53667 x
       have i₂ := eq3554 x x y
       grind)
    | (have i₁ := eq53667 x
       have i₂ := eq3554 x x (M.op (M.op x (σ (σ (M.op x x)))) (M.op x y))
       grind)
    | exact superpose eq3554 eq53667
    | exact resolve eq53667 eq3554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554 eq53667
  have eq54345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq53898 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq53898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq54345
    | exact resolve eq54345 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54345
  have eq54359 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq54346
       have r₂ := eq27
       grind)
    | exact resolve eq54346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54346
  have eq54365 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq54359 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq54359
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq54359
       grind)
    | exact resolve eq12 eq54359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54367 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq54359 eq14
    | exact resolve eq14 eq54359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54359
  have eq54379 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq54365
  have eq54709 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq54367 eq54
    | exact resolve eq54 eq54367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq54367
  have eq54854 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (τ (τ (M.op X0 X0)))) (M.op (σ x) (σ y))) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq54709 eq1141
    | exact resolve eq1141 eq54709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq54709
  have eq55067 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq54854 x
       have i₂ := eq6895 x sF2 sF3
       grind)
    | (have i₁ := eq54854 x
       have i₂ := eq6895 x x (M.op (M.op sF2 (τ (τ (M.op x x)))) (M.op sF2 sF3))
       grind)
    | exact superpose eq6895 eq54854
    | exact resolve eq54854 eq6895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6895 eq54854
  have eq121583 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq54379 eq53898
    | exact resolve eq53898 eq54379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54379
  have eq121592 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq121583
  have eq121612 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq121592 eq4780
    | (have r₁ := eq4780
       have r₂ := eq121592
       grind)
    | exact resolve eq4780 eq121592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4780 eq121592
  have eq121849 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq121612
  have eq122221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq121849 eq53898
    | exact resolve eq53898 eq121849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53898 eq121849
  have eq122231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq122221
  have eq122235 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq122231
       have r₂ := eq27
       grind)
    | exact resolve eq122231 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122231
  have eq122250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq122235 eq55067
    | exact resolve eq55067 eq122235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55067 eq122235
  have eq122540 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq122250
  have eq122596 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq122540
       have r₂ := eq27
       grind)
    | exact resolve eq122540 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122540
  have eq122625 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq122596
       grind)
    | exact superpose eq122596 eq127
    | exact resolve eq127 eq122596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq122642 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 y
       have i₂ := eq122596
       grind)
    | exact superpose eq122596 eq14
    | exact resolve eq14 eq122596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122644 : y = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq122596
       grind)
    | exact superpose eq122596 eq52
    | exact resolve eq52 eq122596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq122658 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq601 X1 X0 y X2
       have i₂ := eq122596
       grind)
    | exact superpose eq122596 eq601
    | exact resolve eq601 eq122596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq122864 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq122625
    | exact resolve eq122625 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122625
  have eq123697 : (σ y) = (M.op (M.op (σ y) (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq122864 eq122642
    | exact resolve eq122642 eq122864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122864
  have eq124029 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ y) (M.op x y)) (M.op X0 X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq123697 eq14
    | exact resolve eq14 eq123697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123697
  have eq328696 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (σ X0) (M.op (M.op (σ X0) (M.op x y)) (M.op X1 X1))) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (M.op X2 X2)) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9990 X0 X1 X2
       have i₂ := eq122658 (σ X0) (M.op X1 X1) X2
       grind)
    | exact superpose eq122658 eq9990
    | (have j0 := eq9990 X0 X1 X2
       grind)
    | exact resolve eq9990 eq122658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9990
  have eq328697 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) (M.op (M.op (σ X0) (M.op x y)) (M.op X1 X1))) ∨ (σ (M.op X0 X0)) = (M.op (M.op (σ X0) (M.op x y)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq328696 X0 X1 x
       have i₂ := eq122658 (σ X0) (M.op X1 X1) x
       grind)
    | exact superpose eq122658 eq328696
    | (have j0 := eq328696 X0 X1 x
       grind)
    | exact resolve eq328696 eq122658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328696
  have eq329510 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (σ X0) (M.op (M.op (σ X0) (M.op x y)) (M.op X2 X2))) ∨ (σ (M.op X0 X0)) ≠ (M.op (M.op (σ X0) (M.op X1 X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10485 X0 X1 X2
       have i₂ := eq122658 (σ X0) (M.op X2 X2) X1
       grind)
    | exact superpose eq122658 eq10485
    | (have j0 := eq10485 X0 X1 X2
       grind)
    | exact resolve eq10485 eq122658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10485
  have eq329511 : ∀ X0 X2 : G, (σ (M.op X0 X0)) ≠ (M.op (M.op (σ X0) (M.op x y)) (M.op X2 X2)) ∨ (M.op X2 X2) = (k (σ X0) (M.op (M.op (σ X0) (M.op x y)) (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq329510 X0 x X2
       have i₂ := eq122658 (σ X0) (M.op X2 X2) x
       grind)
    | exact superpose eq122658 eq329510
    | (have j0 := eq329510 X0 x X2
       grind)
    | exact resolve eq329510 eq122658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122658 eq329510
  have eq329512 : ∀ X0 X2 : G, (M.op X2 X2) = (k (σ X0) (M.op (M.op (σ X0) (M.op x y)) (M.op X2 X2))) := by
    intro X0 X2
    first
    | (have j0 := eq329511 X0 X2
       have j1 := eq328697 X0 X2
       grind)
    | (have r₁ := eq329511 X0 x
       have r₂ := eq328697 X0 x
       grind)
    | exact resolve eq329511 eq328697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328697 eq329511
  have eq329985 : ∀ X0 : G, (M.op x y) = (k (σ X0) (M.op (M.op (σ X0) (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq329512 X0 y
       have i₂ := eq122596
       grind)
    | exact superpose eq122596 eq329512
    | exact resolve eq329512 eq122596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122596 eq329512
  have eq330220 : ∀ X0 : G, (M.op x y) = (k X0 (M.op (M.op X0 (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq329985 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq329985
    | exact resolve eq329985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329985
  have eq330751 : (M.op x y) = (k x y) := by
    first
    | exact superpose eq122644 eq330220
    | exact resolve eq330220 eq122644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122644 eq330220
  have eq331309 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq330751
       grind)
    | exact superpose eq330751 eq44
    | exact resolve eq44 eq330751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq330751
  have eq331391 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq331309
    | exact resolve eq331309 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq331309
  have eq333128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq331391 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq331391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq331391
  have eq333143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq333128
    | exact resolve eq333128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333128
  have eq333161 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq333143
       have r₂ := eq27
       grind)
    | exact resolve eq333143 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333143
  have eq333205 : (σ x) = (M.op (M.op (σ y) (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq333161 eq122642
    | exact resolve eq122642 eq333161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122642 eq333161
  have eq354684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq333205 eq124029
    | exact resolve eq124029 eq333205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124029 eq333205
  have eq354759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq354684
    | exact resolve eq354684 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq354684
  have eq354768 : False := by grind
  exact eq354768

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq427 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq445 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq446 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq445 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq452 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq446 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq446 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq446 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq461 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq452
    | (have j0 := eq452 X0 X1
       grind)
    | exact resolve eq452 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq462 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq461 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq467 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq462 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq462
    | exact resolve eq462 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq462 x y
       grind)
    | exact superpose eq462 eq16
    | exact resolve eq16 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq588 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq467 X0 (τ X1)
       grind)
    | exact superpose eq467 eq17
    | exact resolve eq17 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq467
  have eq604 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq588 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq588
    | exact resolve eq588 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq611 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq604 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq604
    | exact resolve eq604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq623 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq478
       have i₂ := eq611 x y
       grind)
    | exact superpose eq611 eq478
    | exact resolve eq478 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq611
  have eq624 : False := by grind
  exact eq624

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X1) = (k X1 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X2
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
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq42 X0 X1 X2 X3
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X1 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X1) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq223 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq21 X1 X1 (M.op X1 X2)
       have i₂ := eq19 X1 X1 X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq1626 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1637 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1626 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1626 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1626 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq3690 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1637 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq4924 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X1 X0 x (M.op X1 X0)
       have i₂ := eq64 X1 X0 (M.op X1 X0) (M.op X0 x)
       grind)
    | exact superpose eq64 eq223
    | (have j1 := eq64 X1 X0 x x
       grind)
    | exact resolve eq223 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq223
  have eq4998 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4924 X0 X1
       have j1 := eq3690 X0 X1
       grind)
    | (have r₁ := eq4924 X0 X1
       have r₂ := eq3690 X0 X1
       grind)
    | (have r₁ := eq4924 X1 X0
       have r₂ := eq3690 X0 X1
       grind)
    | exact resolve eq4924 eq3690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690 eq4924
  have eq94634 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4998 (σ X0) (σ X1)
       grind)
    | exact superpose eq4998 eq15
    | exact resolve eq15 eq4998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94653 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94634 X0 X1
       have i₂ := eq4998 X0 X1
       grind)
    | exact superpose eq4998 eq94634
    | exact resolve eq94634 eq4998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4998 eq94634
  have eq94680 : False := by grind
  exact eq94680

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq75 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq747 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq12764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12764
    | exact resolve eq12764 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12764
  have eq12776 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12765
       have r₂ := eq28
       grind)
    | exact resolve eq12765 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12765
  have eq12778 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12776
    | exact resolve eq12776 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12776
  have eq12784 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq12778
  have eq12826 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12784
    | exact resolve eq12784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12784
  have eq12906 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12826 eq115
    | exact resolve eq115 eq12826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12826
  have eq12918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12906
  have eq12920 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12918
       have r₂ := eq28
       grind)
    | exact resolve eq12918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12918
  have eq12927 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12920
  have eq12971 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12927
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12927
    | exact resolve eq12927 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12927
  have eq13111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12971
       grind)
    | exact superpose eq12971 eq45
    | exact resolve eq45 eq12971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12971
  have eq13133 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13111
    | exact resolve eq13111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13111
  have eq13324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13133 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13324
    | exact resolve eq13324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13324
  have eq13338 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13327
       have r₂ := eq28
       grind)
    | exact resolve eq13327 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13327
  have eq13340 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13338
    | exact resolve eq13338 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13338
  have eq13341 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13340
  have eq13348 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13341
  have eq13392 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13348
    | exact resolve eq13348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13348
  have eq13543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13392 eq13133
    | exact resolve eq13133 eq13392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13133 eq13392
  have eq13549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13543
  have eq13553 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13549
       have r₂ := eq28
       grind)
    | exact resolve eq13549 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13549
  have eq13669 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13553 eq28
    | exact resolve eq28 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13671 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13553 eq76
    | (have r₁ := eq76
       have r₂ := eq13553
       grind)
    | exact resolve eq76 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq13553
  have eq13678 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13671
  have eq14302 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13678 eq115
    | exact resolve eq115 eq13678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14322 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq14302
  have eq14336 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14322
       have r₂ := eq13669
       grind)
    | exact resolve eq14322 eq13669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14322
  have eq14348 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq14336
  have eq14394 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14348
    | exact resolve eq14348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14348
  have eq14750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14394 eq115
    | exact resolve eq115 eq14394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14394
  have eq14766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq14750
  have eq14770 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14766
       have r₂ := eq28
       grind)
    | exact resolve eq14766 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14766
  have eq14777 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq14770
  have eq14821 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14777
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14777
    | exact resolve eq14777 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14777
  have eq14965 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq14821
       grind)
    | exact superpose eq14821 eq45
    | exact resolve eq45 eq14821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14821
  have eq14989 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq14965
    | exact resolve eq14965 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14965
  have eq15171 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14989 eq13678
    | exact resolve eq13678 eq14989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13678
  have eq15179 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15171
  have eq15187 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15179
       have r₂ := eq13669
       grind)
    | exact resolve eq15179 eq13669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13669 eq15179
  have eq15209 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15187
  have eq15255 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq15209
    | exact resolve eq15209 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15209
  have eq15435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15255 eq14989
    | exact resolve eq14989 eq15255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14989 eq15255
  have eq15441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15435
  have eq15449 : x = (M.op x y) := by
    first
    | (have r₁ := eq15441
       have r₂ := eq28
       grind)
    | exact resolve eq15441 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15441
  have eq15569 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15449 eq21
    | exact resolve eq21 eq15449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq15575 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq15449 eq75
    | (have r₁ := eq75
       have r₂ := eq15449
       grind)
    | exact resolve eq75 eq15449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq15631 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq15575
  have eq15685 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15569
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15569
    | exact resolve eq15569 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15569
  have eq15687 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15685 eq27
    | exact resolve eq27 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17187 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq15631
       grind)
    | exact superpose eq15631 eq45
    | exact resolve eq45 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17201 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq747 x y
       have i₂ := eq15631
       grind)
    | exact superpose eq15631 eq747
    | (have j0 := eq747 x y
       grind)
    | exact resolve eq747 eq15631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15631
  have eq17204 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq17201
  have eq17211 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17204
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17204
    | exact resolve eq17204 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17204
  have eq17223 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15685 eq17187
    | exact resolve eq17187 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17187
  have eq17225 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17211
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17211
    | exact resolve eq17211 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17211
  have eq17237 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17223
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17223
    | exact resolve eq17223 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17223
  have eq17238 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17225
    | exact resolve eq17225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17225
  have eq17247 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15685 eq17237
    | exact resolve eq17237 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17237
  have eq17248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15685 eq17238
    | exact resolve eq17238 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17238
  have eq17252 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17248
       have r₂ := eq28
       grind)
    | exact resolve eq17248 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17248
  have eq17256 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17252
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17252
    | exact resolve eq17252 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252
  have eq17260 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17256
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17256
    | exact resolve eq17256 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17256
  have eq17264 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15685 eq17260
    | exact resolve eq17260 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17260
  have eq17343 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq17264
  have eq17391 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15687 eq17343
    | exact resolve eq17343 eq15687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17343
  have eq17425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17391 eq17247
    | exact resolve eq17247 eq17391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17247 eq17391
  have eq17431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq17425
  have eq17433 : x = (M.op y y) := by
    first
    | (have r₁ := eq17431
       have r₂ := eq28
       grind)
    | exact resolve eq17431 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17431
  have eq17453 : (M.op x y) = (k x y) := by grind
  clear eq17433
  have eq17497 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq17453
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17453
    | exact resolve eq17453 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17453
  have eq17521 : x = (k x y) := by
    first
    | exact superpose eq15449 eq17497
    | exact resolve eq17497 eq15449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15449 eq17497
  have eq17619 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq17521
       grind)
    | exact superpose eq17521 eq45
    | exact resolve eq45 eq17521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq17633 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq747 x y
       have i₂ := eq17521
       grind)
    | exact superpose eq17521 eq747
    | (have j0 := eq747 x y
       grind)
    | exact resolve eq747 eq17521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq17521
  have eq17636 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq17633
  have eq17642 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17636
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17636
    | exact resolve eq17636 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17636
  have eq17654 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15685 eq17619
    | exact resolve eq17619 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17619
  have eq17655 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17642
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17642
    | exact resolve eq17642 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17642
  have eq17667 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq17654
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17654
    | exact resolve eq17654 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17654
  have eq17668 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq17655
    | exact resolve eq17655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17655
  have eq17677 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15685 eq17667
    | exact resolve eq17667 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17667
  have eq17678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq15685 eq17668
    | exact resolve eq17668 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17668
  have eq17682 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq17678
       have r₂ := eq28
       grind)
    | exact resolve eq17678 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17678
  have eq17686 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17682
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17682
    | exact resolve eq17682 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17682
  have eq17690 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17686
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17686
    | exact resolve eq17686 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17686
  have eq17694 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq15685 eq17690
    | exact resolve eq17690 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15685 eq17690
  have eq17811 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq17694
  have eq17855 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15687 eq17811
    | exact resolve eq17811 eq15687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15687 eq17811
  have eq17859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17677 eq17855
    | exact resolve eq17855 eq17677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17677 eq17855
  have eq17862 : False := by grind
  exact eq17862

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq14 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
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
  have eq120 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq43
    | exact resolve eq43 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq127 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq120
  have eq259 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 : G, (M.op (M.op x x) x) = (M.op (M.op x y) (M.op X0 (M.op (M.op x x) x))) := by
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
  clear eq18
  have eq924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq107 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq924
    | exact resolve eq924 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq928 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq925
       have r₂ := eq27
       grind)
    | exact resolve eq925 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq930 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq928
    | exact resolve eq928 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq938 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq930 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq930
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq930
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq930
       grind)
    | exact resolve eq12 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq938
       have r₂ := eq26
       grind)
    | exact resolve eq938 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq1047 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq942 eq107
    | exact resolve eq107 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq1050 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq1047
  have eq1059 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1050 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1050
       grind)
    | exact resolve eq13 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1072 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1059 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq3415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1072 eq107
    | exact resolve eq107 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1072
  have eq3428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq3415
  have eq3437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq3428
    | exact resolve eq3428 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428
  have eq3439 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq3437
       have r₂ := eq27
       grind)
    | exact resolve eq3437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3437
  have eq3443 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3439 eq53
    | exact resolve eq53 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3448 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ (M.op x y)) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq3439 eq50
    | exact resolve eq50 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10957 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq930 eq3448
    | exact resolve eq3448 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930 eq3448
  have eq11046 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq10957 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10957
  have eq11074 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq11046 eq475
    | exact resolve eq475 eq11046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046
  have eq11098 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq11074 eq259
    | exact resolve eq259 eq11074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq11074
  have eq11137 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq3443 eq11098
    | exact resolve eq11098 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443 eq11098
  have eq11157 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq11137
  have eq11174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq11157 eq3439
    | exact resolve eq3439 eq11157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439 eq11157
  have eq11226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq11174
  have eq11243 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq11226
       have r₂ := eq27
       grind)
    | exact resolve eq11226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11226
  have eq11254 : ∀ X0 : G, x = (M.op (M.op (M.op x x) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq11243
       grind)
    | exact superpose eq11243 eq14
    | exact resolve eq14 eq11243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11255 : ∀ X0 : G, (M.op (M.op y y) y) = (M.op (M.op x y) (M.op X0 (M.op (M.op y y) y))) := by
    intro X0
    first
    | (have i₁ := eq50 y x X0
       have i₂ := eq11243
       grind)
    | exact superpose eq11243 eq50
    | exact resolve eq50 eq11243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq11256 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq54 x y x
       have i₂ := eq11243
       grind)
    | exact superpose eq11243 eq54
    | exact resolve eq54 eq11243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq11243
  have eq11388 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq11256 sF0
       have i₂ := eq475 sF0 x
       grind)
    | (have i₁ := eq11256 sF0
       have i₂ := eq475 sF0 sF0
       grind)
    | exact superpose eq475 eq11256
    | exact resolve eq11256 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11256
  have eq11483 : (M.op x y) = (M.op (M.op (M.op (M.op x x) x) (M.op x y)) x) := by
    first
    | exact superpose eq582 eq11388
    | exact resolve eq11388 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq11388
  have eq11515 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq11254 eq11483
    | exact resolve eq11483 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11483
  have eq11517 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq11515
       grind)
    | exact superpose eq11515 eq127
    | exact resolve eq127 eq11515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq11526 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq11254 X0
       have i₂ := eq11515
       grind)
    | exact superpose eq11515 eq11254
    | exact resolve eq11254 eq11515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11254 eq11515
  have eq11581 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq11517
    | exact resolve eq11517 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11517
  have eq17289 : (M.op (M.op (M.op y y) y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq11255 eq475
    | exact resolve eq475 eq11255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq11255
  have eq17304 : x = (M.op (M.op (M.op y y) y) (M.op x y)) := by
    first
    | exact superpose eq11526 eq17289
    | exact resolve eq17289 eq11526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11526 eq17289
  have eq17320 : x = y := by
    first
    | exact superpose eq52 eq17304
    | exact resolve eq17304 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq17304
  have eq17334 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17320
       grind)
    | exact superpose eq17320 eq24
    | exact resolve eq24 eq17320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17320
  have eq17400 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17334
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17334
    | exact resolve eq17334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17334
  have eq17413 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17400 eq26
    | exact resolve eq26 eq17400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17400
  have eq17489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11581 eq17413
    | exact resolve eq17413 eq11581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11581 eq17413
  have eq17495 : False := by grind
  exact eq17495
