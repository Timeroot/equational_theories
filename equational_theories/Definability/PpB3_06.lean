import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X1)) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq35 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq24
    | exact resolve eq24 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op X1 (M.op X0 X1))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X1 (M.op X0 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X1 (M.op X0 X1)) X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq104 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq117 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ X0)
       have i₂ := eq107 (τ X0)
       grind)
    | exact superpose eq107 eq20
    | (have j1 := eq107 (τ X0)
       grind)
    | exact resolve eq20 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq107 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117
    | (have j0 := eq117 X0
       grind)
    | exact resolve eq117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq125 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq119
    | (have j0 := eq119 X0
       grind)
    | exact resolve eq119 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq170 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq64 (M.op X0 X0) X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq64
    | (have j1 := eq104 X0
       grind)
    | exact resolve eq64 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq104
  have eq191 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq192 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq65
  have eq762 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq887 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq11
    | (have j1 := eq125 X0
       grind)
    | exact resolve eq11 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq899 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq887 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq887
    | (have j0 := eq887 X0
       grind)
    | exact resolve eq887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq993 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq899 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq899
    | (have j0 := eq899 X0
       have j1 := eq107 X0
       grind)
    | exact resolve eq899 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1006 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k X0 (τ (σ X0)))) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (σ X0) X1
       have i₂ := eq899 (σ X0)
       grind)
    | exact superpose eq899 eq35
    | (have j1 := eq899 (σ X0)
       grind)
    | exact resolve eq35 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq899
  have eq1021 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1006 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1006
    | (have j0 := eq1006 X0 X1
       grind)
    | exact resolve eq1006 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1033 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq993 X0
       have j1 := eq118 X0
       grind)
    | (have r₁ := eq993 X0
       have r₂ := eq118 X0
       grind)
    | exact resolve eq993 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq993
  have eq1040 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (k X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1021 X0 X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq1021
    | (have j0 := eq1021 X0 X1
       grind)
    | exact resolve eq1021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1054 : ∀ X0 X1 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k (τ X1) X0) = (k (τ X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1040
    | (have j0 := eq1040 X0 X1
       grind)
    | exact resolve eq1040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1063 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1054 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1054
    | (have j0 := eq1054 X0 X1
       grind)
    | exact resolve eq1054 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1085 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq1033 (σ X0)
       grind)
    | exact superpose eq1033 eq30
    | (have j1 := eq1033 (σ X0)
       grind)
    | exact resolve eq30 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1033
  have eq1093 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq1085 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1085
    | (have j0 := eq1085 X0
       grind)
    | exact resolve eq1085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1110 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1093 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1093
    | (have j0 := eq1093 X0
       grind)
    | exact resolve eq1093 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq12550 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq762 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq762
    | (have j0 := eq762 (σ X0) (σ X1)
       grind)
    | exact resolve eq762 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12557 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq762 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq762
    | (have j0 := eq762 (τ X0) (τ X1)
       grind)
    | exact resolve eq762 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12613 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12557 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq12557
    | (have j0 := eq12557 X0 X1
       grind)
    | exact resolve eq12557 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12557
  have eq12629 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12613 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12613
    | (have j0 := eq12613 X0 X1
       grind)
    | exact resolve eq12613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12613
  have eq12642 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12629 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12629
    | (have j0 := eq12629 X0 X1
       grind)
    | exact resolve eq12629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12629
  have eq12645 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12642 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12642
    | (have j0 := eq12642 X0 X1
       grind)
    | exact resolve eq12642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12642
  have eq12646 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12645 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12645
    | (have j0 := eq12645 X0 X1
       grind)
    | exact resolve eq12645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12645
  have eq12647 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12646 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12646
    | (have j0 := eq12646 X0 X1
       grind)
    | exact resolve eq12646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12646
  have eq29962 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (k X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1063 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1063
    | (have j0 := eq1063 X1 X1
       grind)
    | exact resolve eq1063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq30131 : ∀ X0 X1 X2 : G, (k (τ X1) (k X0 X0)) = (τ (k X1 (σ (M.op X0 X0)))) ∨ (k X2 X0) = (k X2 (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (k X0 X0)
       have i₂ := eq29962 X2 X0
       grind)
    | exact superpose eq29962 eq24
    | (have j1 := eq29962 X2 X0
       grind)
    | exact resolve eq24 eq29962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29962
  have eq30198 : ∀ X0 X1 X2 : G, (k (τ X1) (k X0 X0)) = (k (τ X1) (M.op X0 X0)) ∨ (k X2 X0) = (k X2 (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30131 X0 X1 X2
       have i₂ := eq24 X1 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq30131
    | (have j0 := eq30131 X0 X1 X2
       grind)
    | exact resolve eq30131 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq30131
  have eq53260 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq192 X0 X1
       grind)
    | exact superpose eq192 eq12
    | (have j1 := eq192 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) X0
       have r₂ := eq192 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq192 (M.op X1 (σ X1)) X1
       grind)
    | exact resolve eq12 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq53300 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq53260 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53260
  have eq60357 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53300 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53300
    | exact resolve eq53300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53300
  have eq60632 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq60357 X0 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq60357
    | (have j0 := eq60357 X0 X1
       grind)
    | exact resolve eq60357 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq60357
  have eq60659 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60632 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq60632
    | (have j0 := eq60632 (τ (σ (k X0 X1))) (τ (M.op (σ X1) (σ X0)))
       grind)
    | exact resolve eq60632 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60720 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq60632 X1 X0
       grind)
    | exact superpose eq60632 eq11
    | (have j1 := eq60632 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq60632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60632
  have eq60917 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60720 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq60720
    | (have j0 := eq60720 X0 X1
       grind)
    | exact resolve eq60720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60720
  have eq60938 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60659 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq60659
    | (have j0 := eq60659 X0 X1
       grind)
    | exact resolve eq60659 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60659
  have eq61033 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq60917 (τ X0) X1
       grind)
    | exact superpose eq60917 eq20
    | (have j1 := eq60917 (τ X0) X1
       grind)
    | exact resolve eq20 eq60917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq60917
  have eq61954 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61033 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61033
    | exact resolve eq61033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61033
  have eq62155 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61954 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq61954
    | (have j0 := eq61954 X0 X1
       grind)
    | exact resolve eq61954 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61954
  have eq173492 : ∀ X0 X1 X2 : G, (k X2 X1) = (k X2 (k X1 X1)) ∨ (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30198 X0 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30198
    | (have j0 := eq30198 X1 X1 X2
       grind)
    | exact resolve eq30198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30198
  have eq174199 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (k X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq173492 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173492
  have eq174466 : ∀ X0 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq174199 (M.op X0 X0) X0
       have i₂ := eq170 X0
       grind)
    | exact superpose eq170 eq174199
    | (have j1 := eq170 X0
       grind)
    | exact resolve eq174199 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq174199
  have eq174494 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq174466 X0
       have j1 := eq398 X0
       grind)
    | (have r₁ := eq174466 X0
       have r₂ := eq398 X0
       grind)
    | exact resolve eq174466 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq174466
  have eq176757 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (M.op (k X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12647 (M.op X0 X0) (k X0 X0)
       have i₂ := eq174494 X0
       grind)
    | exact superpose eq174494 eq12647
    | (have j0 := eq12647 (M.op X0 X0) (k X0 X0)
       have j1 := eq174494 X0
       grind)
    | (have r₁ := eq12647 (M.op X0 X0) (k X0 X0)
       have r₂ := eq174494 X0
       grind)
    | exact resolve eq12647 eq174494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174494
  have eq176774 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (M.op (k X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq176757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176757
  have eq176775 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq176774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176774
  have eq219566 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq60938 X0 X1
       grind)
    | exact superpose eq60938 eq10
    | (have j1 := eq60938 X0 X1
       grind)
    | exact resolve eq10 eq60938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60938
  have eq219773 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq219566 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq219566
    | (have j0 := eq219566 X0 X1
       grind)
    | exact resolve eq219566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219566
  have eq220336 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (σ X1) = X0 ∨ (τ X0) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq219773 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219773
    | (have j0 := eq219773 (τ X0) X1
       grind)
    | exact resolve eq219773 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220502 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq219773 X0 X1
       grind)
    | exact superpose eq219773 eq11
    | (have j1 := eq219773 X0 X1
       grind)
    | exact resolve eq11 eq219773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219773
  have eq224461 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq220502 y x
       grind)
    | exact superpose eq220502 eq16
    | (have j1 := eq220502 x y
       grind)
    | exact resolve eq16 eq220502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220502
  have eq224824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq224461
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq224461
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq224461
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq224461
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq224461 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq224461
       have i₂ := eq62155 x y
       grind)
    | exact superpose eq62155 eq224461
    | (have j1 := eq62155 x y
       grind)
    | (have r₁ := eq224461
       have r₂ := eq62155 x y
       grind)
    | (have r₁ := eq224461
       have r₂ := eq62155 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq224461
       have r₂ := eq62155 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq224461 eq62155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62155 eq224461
  have eq224829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq224826
  have eq224830 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq224829
  have eq224832 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq224824
  have eq224833 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq224832
  have eq224836 : y = (k y x) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq224830
       grind)
    | exact superpose eq224830 eq16
    | exact resolve eq16 eq224830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224830
  have eq224837 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq224833
       grind)
    | exact superpose eq224833 eq16
    | exact resolve eq16 eq224833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224833
  have eq225804 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq762 x y
       have i₂ := eq224836
       grind)
    | exact superpose eq224836 eq762
    | (have j0 := eq762 x y
       grind)
    | exact resolve eq762 eq224836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225819 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq225804
  have eq225820 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq225819
  have eq225827 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq224837
       have i₂ := eq1110 x
       grind)
    | exact superpose eq1110 eq224837
    | (have j1 := eq1110 x
       grind)
    | (have r₁ := eq224837
       have r₂ := eq1110 x
       grind)
    | exact resolve eq224837 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224837
  have eq225858 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq225827
  have eq225869 : y ≠ y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq225858
       grind)
    | exact superpose eq225858 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq225858
       grind)
    | exact resolve eq12 eq225858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225899 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq225869
  have eq225906 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq762 x y
       have i₂ := eq225899
       grind)
    | exact superpose eq225899 eq762
    | (have j0 := eq762 x y
       grind)
    | exact resolve eq762 eq225899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225899
  have eq225921 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by grind
  clear eq225906
  have eq225922 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq225921
  have eq226574 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq225922
       grind)
    | exact superpose eq225922 eq16
    | exact resolve eq16 eq225922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225922
  have eq226650 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq226574
       have i₂ := eq225858
       grind)
    | exact superpose eq225858 eq226574
    | exact resolve eq226574 eq225858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225858 eq226574
  have eq226671 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq226650
  have eq226672 : (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq226671
  have eq226678 : y = (τ (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq226672
       grind)
    | exact superpose eq226672 eq10
    | exact resolve eq10 eq226672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226672
  have eq226888 : x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq226678
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq226678
    | exact resolve eq226678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226678
  have eq226889 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq226888
       grind)
    | exact superpose eq226888 eq16
    | exact resolve eq16 eq226888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226888
  have eq226890 : x = (k x x) := by
    first
    | (have j1 := eq1110 x
       grind)
    | (have r₁ := eq226889
       have r₂ := eq1110 x
       grind)
    | exact resolve eq226889 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq226889
  have eq226952 : (M.op x x) = (M.op x (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq176775 x
       have i₂ := eq226890
       grind)
    | exact superpose eq226890 eq176775
    | exact resolve eq176775 eq226890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176775
  have eq227953 : x = (M.op x x) ∨ (M.op x x) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq18 x x
       have i₂ := eq226952
       grind)
    | exact superpose eq226952 eq18
    | exact resolve eq18 eq226952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq226952
  have eq228907 : x = (M.op (M.op x x) x) ∨ (M.op x x) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq9 x x
       have i₂ := eq227953
       grind)
    | exact superpose eq227953 eq9
    | exact resolve eq9 eq227953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227953
  have eq231931 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x x) = (k x x) := by grind
  clear eq228907
  have eq231963 : x = (M.op x x) ∨ (M.op x x) = (k x x) := by grind
  clear eq231931
  have eq231986 : (M.op x x) = (k x x) := by
    first
    | (have j1 := eq12 x x
       grind)
    | (have r₁ := eq231963
       have r₂ := eq12 x x
       grind)
    | exact resolve eq231963 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231963
  have eq231989 : x = (M.op x x) := by
    first
    | (have i₁ := eq231986
       have i₂ := eq226890
       grind)
    | exact superpose eq226890 eq231986
    | exact resolve eq231986 eq226890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231986
  have eq580133 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ (σ y)) = (M.op (σ (σ x)) (σ (σ y))) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12550 y x
       have i₂ := eq224836
       grind)
    | exact superpose eq224836 eq12550
    | (have j0 := eq12550 x y
       grind)
    | exact resolve eq12550 eq224836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224836
  have eq580289 : (σ (σ x)) = (σ (σ y)) ∨ (σ (σ y)) = (M.op (σ (σ x)) (σ (σ y))) ∨ (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq580133
  have eq580579 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ (σ y)) = (M.op (σ (σ x)) (σ (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq580289
       have i₂ := eq231989
       grind)
    | exact superpose eq231989 eq580289
    | exact resolve eq580289 eq231989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580289
  have eq1486584 : (σ x) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq225820
  have eq1486594 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1486584
       have i₂ := eq231989
       grind)
    | exact superpose eq231989 eq1486584
    | exact resolve eq1486584 eq231989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486584
  have eq1486595 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq1486594
  have eq1486628 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1486595
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1486595
    | exact resolve eq1486595 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486595
  have eq1486659 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1486628
       have i₂ := eq226890
       grind)
    | exact superpose eq226890 eq1486628
    | exact resolve eq1486628 eq226890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486628
  have eq1486687 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq220336 (σ y) x
       have i₂ := eq1486659
       grind)
    | exact superpose eq1486659 eq220336
    | (have j0 := eq220336 (σ y) x
       grind)
    | exact resolve eq220336 eq1486659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486659
  have eq1486753 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1486687
  have eq1486796 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1486753
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1486753
    | exact resolve eq1486753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486753
  have eq1487914 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ (σ y)) = (M.op (σ (σ x)) (σ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12550 y x
       have i₂ := eq1486796
       grind)
    | exact superpose eq1486796 eq12550
    | (have j0 := eq12550 x y
       grind)
    | exact resolve eq12550 eq1486796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12550 eq1486796
  have eq1487939 : (σ (σ x)) = (σ (σ y)) ∨ (σ (σ y)) = (M.op (σ (σ x)) (σ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1487914
  have eq1487947 : (σ (σ y)) = (M.op (σ (σ x)) (σ (σ y))) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1487939
       have r₂ := eq580579
       grind)
    | exact resolve eq1487939 eq580579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580579 eq1487939
  have eq1721515 : (τ (σ (σ y))) = (k (τ (σ (σ y))) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (τ (σ (σ y))) = (k (τ (σ (σ y))) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq220336 (σ (σ y)) (σ x)
       have i₂ := eq1487947
       grind)
    | exact superpose eq1487947 eq220336
    | (have j0 := eq220336 (σ (σ y)) (σ x)
       grind)
    | exact resolve eq220336 eq1487947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220336 eq1487947
  have eq1721579 : (τ (σ (σ y))) = (k (τ (σ (σ y))) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1721515
  have eq1721625 : (σ y) = (k (σ y) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1721579
       have i₂ := eq10 (σ y)
       grind)
    | exact superpose eq10 eq1721579
    | exact resolve eq1721579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721579
  have eq1721675 : (σ x) = (σ y) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1721625
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1721625
    | exact resolve eq1721625 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721625
  have eq1721727 : y = (τ (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1721675
       grind)
    | exact superpose eq1721675 eq10
    | exact resolve eq10 eq1721675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721675
  have eq1722267 : x = y ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1721727
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1721727
    | exact resolve eq1721727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721727
  have eq1722268 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1722267
       grind)
    | exact superpose eq1722267 eq16
    | exact resolve eq16 eq1722267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722267
  have eq1722285 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1722268
       have i₂ := eq231989
       grind)
    | exact superpose eq231989 eq1722268
    | exact resolve eq1722268 eq231989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722268
  have eq1724656 : (σ x) ≠ (σ x) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  have eq1724657 : (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq1724656
  have eq1724658 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1724657
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1724657
    | exact resolve eq1724657 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724657
  have eq1724749 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1724658
       have i₂ := eq226890
       grind)
    | exact superpose eq226890 eq1724658
    | exact resolve eq1724658 eq226890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724658
  have eq1724765 : (σ (σ x)) = (σ (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq1724749
       have r₂ := eq1722285
       grind)
    | exact resolve eq1724749 eq1722285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722285 eq1724749
  have eq1724813 : (σ y) = (τ (σ (σ x))) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 (σ y)
       have i₂ := eq1724765
       grind)
    | exact superpose eq1724765 eq10
    | exact resolve eq10 eq1724765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724765
  have eq1725676 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1724813
       have i₂ := eq10 (σ x)
       grind)
    | exact superpose eq10 eq1724813
    | exact resolve eq1724813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724813
  have eq1725965 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1725676
       grind)
    | exact superpose eq1725676 eq10
    | exact resolve eq10 eq1725676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725676
  have eq1726506 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1725965
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1725965
    | exact resolve eq1725965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725965
  have eq1726507 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1726506
       grind)
    | exact superpose eq1726506 eq16
    | exact resolve eq16 eq1726506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726506
  have eq1726524 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1726507
       have i₂ := eq231989
       grind)
    | exact superpose eq231989 eq1726507
    | exact resolve eq1726507 eq231989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726507
  have eq1726579 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  have eq1726580 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq1726579
  have eq1726581 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1726580
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1726580
    | exact resolve eq1726580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726580
  have eq1726672 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1726581
       have i₂ := eq226890
       grind)
    | exact superpose eq226890 eq1726581
    | exact resolve eq1726581 eq226890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726581
  have eq1726688 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq1726672
       have r₂ := eq1726524
       grind)
    | exact resolve eq1726672 eq1726524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726524 eq1726672
  have eq1726712 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq762 x y
       have i₂ := eq1726688
       grind)
    | exact superpose eq1726688 eq762
    | (have j0 := eq762 x y
       grind)
    | (have r₁ := eq762 x y
       have r₂ := eq1726688
       grind)
    | exact resolve eq762 eq1726688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1726722 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1726688
       grind)
    | exact superpose eq1726688 eq10
    | exact resolve eq10 eq1726688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726688
  have eq1727248 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1726712
  have eq1727266 : y = (k y x) := by
    first
    | (have i₁ := eq1726722
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1726722
    | exact resolve eq1726722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726722
  have eq1727294 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12647 y x
       have i₂ := eq1727266
       grind)
    | exact superpose eq1727266 eq12647
    | (have j0 := eq12647 x y
       grind)
    | (have r₁ := eq12647 y x
       have r₂ := eq1727266
       grind)
    | exact resolve eq12647 eq1727266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12647 eq1727266
  have eq1727317 : x = y ∨ y = (M.op x y) := by grind
  clear eq1727294
  have eq1727327 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1727317
       grind)
    | exact superpose eq1727317 eq16
    | exact resolve eq16 eq1727317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727317
  have eq1727346 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1727327
       have i₂ := eq231989
       grind)
    | exact superpose eq231989 eq1727327
    | exact resolve eq1727327 eq231989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231989 eq1727327
  have eq1740456 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1727248
       grind)
    | exact superpose eq1727248 eq16
    | exact resolve eq16 eq1727248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727248
  have eq1740983 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  have eq1740984 : y = (M.op x y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq1740983
  have eq1740985 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1740984
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1740984
    | exact resolve eq1740984 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740984
  have eq1741076 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1740985
       have i₂ := eq226890
       grind)
    | exact superpose eq226890 eq1740985
    | exact resolve eq1740985 eq226890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740985
  have eq1741092 : y = (M.op x y) := by
    first
    | (have r₁ := eq1741076
       have r₂ := eq1727346
       grind)
    | exact resolve eq1741076 eq1727346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727346 eq1741076
  have eq1741113 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1740456
       have i₂ := eq1741092
       grind)
    | exact superpose eq1741092 eq1740456
    | exact resolve eq1740456 eq1741092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740456
  have eq1741173 : (σ x) = (σ y) := by grind
  clear eq1741113
  have eq1741203 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1741173
       grind)
    | exact superpose eq1741173 eq16
    | exact resolve eq16 eq1741173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1741746 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1741203
       have i₂ := eq1741092
       grind)
    | exact superpose eq1741092 eq1741203
    | exact resolve eq1741203 eq1741092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741092 eq1741203
  have eq1741747 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1741746
       have i₂ := eq1741173
       grind)
    | exact superpose eq1741173 eq1741746
    | exact resolve eq1741746 eq1741173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741173 eq1741746
  have eq1742106 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  have eq1742107 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq1742106
  have eq1742108 : (σ (k x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1742107
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1742107
    | exact resolve eq1742107 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742107
  have eq1742199 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1742108
       have i₂ := eq226890
       grind)
    | exact superpose eq226890 eq1742108
    | exact resolve eq1742108 eq226890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226890 eq1742108
  have eq1742215 : False := by grind
  exact eq1742215

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq172 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq183 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq184 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq188 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq184
    | (have j0 := eq184 X0 X1
       grind)
    | exact resolve eq184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq189 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq527 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq189 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189
    | exact resolve eq189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq189 x y
       grind)
    | exact superpose eq189 eq16
    | (have j1 := eq189 x y
       grind)
    | exact resolve eq16 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq558 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq527
    | (have j0 := eq527 X0 X1
       grind)
    | exact resolve eq527 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq527
  have eq563 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq558
    | exact resolve eq558 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq638 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq563 (τ X1) X0
       grind)
    | exact superpose eq563 eq19
    | (have j1 := eq563 (τ X1) X0
       grind)
    | exact resolve eq19 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq563
  have eq857 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq638 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq638
    | exact resolve eq638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq910 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq857
    | (have j0 := eq857 X0 X1
       grind)
    | exact resolve eq857 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq541
       have i₂ := eq910 y x
       grind)
    | exact superpose eq910 eq541
    | (have j1 := eq910 (σ y) (σ x)
       grind)
    | (have r₁ := eq541
       have r₂ := eq910 y x
       grind)
    | exact resolve eq541 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq995
  have eq1020 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq996
  have eq1031 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq541
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq541
    | exact resolve eq541 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq1020
  have eq1032 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1031
  have eq1033 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1032
  have eq1078 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1033
  have eq1091 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1078
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1078
    | exact resolve eq1078 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1096 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1091
       grind)
    | exact superpose eq1091 eq16
    | exact resolve eq16 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1096
       have i₂ := eq910 y x
       grind)
    | exact superpose eq910 eq1096
    | (have j1 := eq910 y x
       grind)
    | (have r₁ := eq1096
       have r₂ := eq910 y x
       grind)
    | exact resolve eq1096 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1150 : y = (M.op x x) := by grind
  clear eq1149
  have eq1157 : (M.op x y) = (k y x) := by grind
  clear eq1150
  have eq1232 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1096
       have i₂ := eq1157
       grind)
    | exact superpose eq1157 eq1096
    | exact resolve eq1096 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq1157
  have eq1235 : False := by grind
  exact eq1235

/-- `Equation221`: `x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation221 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law221 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law221.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq77 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq128 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq622 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq128 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq128
    | (have j0 := eq128 (σ X1) (σ X0)
       grind)
    | exact resolve eq128 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq3750 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq77 (σ X1) X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3769 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq3770 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769
  have eq3771 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3750 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750
  have eq3772 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3771 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771
  have eq3774 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3770 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3770
    | (have j0 := eq3770 X0
       grind)
    | exact resolve eq3770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq3838 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq3774 X0
       grind)
    | exact superpose eq3774 eq38
    | (have j1 := eq3774 X0
       grind)
    | exact resolve eq38 eq3774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3774
  have eq3853 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3838 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3838
    | (have j0 := eq3838 X0
       grind)
    | exact resolve eq3838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3838
  have eq3854 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq3856 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3854 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3854
    | exact resolve eq3854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3880 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3854 X0
       grind)
    | exact superpose eq3854 eq11
    | exact resolve eq11 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq3931 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3856 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3856
    | exact resolve eq3856 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3856
  have eq4164 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3931 X0
       grind)
    | exact superpose eq3931 eq11
    | exact resolve eq11 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4255 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4164 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4164
    | exact resolve eq4164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4164
  have eq4319 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq4255 (τ X0)
       grind)
    | exact superpose eq4255 eq34
    | exact resolve eq34 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4371 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4319 X0
       have i₂ := eq3931 X0
       grind)
    | exact superpose eq3931 eq4319
    | exact resolve eq4319 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3931 eq4319
  have eq4922 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq4942 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4922 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq4922
    | exact resolve eq4922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4922
  have eq4980 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4942 X0
       have i₂ := eq4255 X0
       grind)
    | exact superpose eq4255 eq4942
    | exact resolve eq4942 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4942
  have eq5000 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq4980
  have eq31548 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq622 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq622
    | (have j0 := eq622 (τ X0) (τ X1)
       grind)
    | exact resolve eq622 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq31620 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31548 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq31548
    | (have j0 := eq31548 X0 X1
       grind)
    | exact resolve eq31548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31548
  have eq31672 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31620 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31620
    | (have j0 := eq31620 X0 X1
       grind)
    | exact resolve eq31620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31620
  have eq31722 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31672 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31672
    | (have j0 := eq31672 X0 X1
       grind)
    | exact resolve eq31672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31672
  have eq31769 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq31722 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31722
    | (have j0 := eq31722 X0 X1
       grind)
    | exact resolve eq31722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31722
  have eq31809 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31769 X0 X1
       have i₂ := eq3880 (σ (τ X1))
       grind)
    | exact superpose eq3880 eq31769
    | (have j0 := eq31769 X0 X1
       grind)
    | exact resolve eq31769 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31769
  have eq31847 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31809 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq31809
    | (have j0 := eq31809 X0 X1
       grind)
    | exact resolve eq31809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31809
  have eq31883 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31847 X0 X1
       have i₂ := eq20 X1 (τ X1)
       grind)
    | exact superpose eq20 eq31847
    | (have j0 := eq31847 X0 X1
       grind)
    | exact resolve eq31847 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31847
  have eq31912 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31883 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31883
    | (have j0 := eq31883 X0 X1
       grind)
    | exact resolve eq31883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31883
  have eq31937 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31912 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31912
    | (have j0 := eq31912 X0 X1
       grind)
    | exact resolve eq31912 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31912
  have eq31962 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31937 X0 X1
       have i₂ := eq4255 X1
       grind)
    | exact superpose eq4255 eq31937
    | (have j0 := eq31937 X0 X1
       grind)
    | exact resolve eq31937 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31937
  have eq42940 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) X0
       have i₂ := eq3772 (σ X0) X1
       grind)
    | exact superpose eq3772 eq24
    | (have j1 := eq3772 (σ X0) X1
       grind)
    | exact resolve eq24 eq3772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3772
  have eq43031 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42940 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq42940
    | (have j0 := eq42940 X0 X1
       grind)
    | exact resolve eq42940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42940
  have eq43119 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43031 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43031
    | (have j0 := eq43031 X0 X1
       grind)
    | exact resolve eq43031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43031
  have eq43198 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43119 X0 X1
       have i₂ := eq3880 X0
       grind)
    | exact superpose eq3880 eq43119
    | (have j0 := eq43119 X0 X1
       grind)
    | exact resolve eq43119 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3880 eq43119
  have eq43252 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43198 X0 X1
       have i₂ := eq4255 X0
       grind)
    | exact superpose eq4255 eq43198
    | (have j0 := eq43198 X0 X1
       grind)
    | exact resolve eq43198 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4255 eq43198
  have eq43296 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43252 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq43252
    | (have j0 := eq43252 X0 X1
       grind)
    | exact resolve eq43252 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43252
  have eq48970 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43296 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43296
    | (have j0 := eq43296 X1 (τ X0)
       grind)
    | exact resolve eq43296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49038 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq43296 X1 X0
       grind)
    | exact superpose eq43296 eq11
    | (have j1 := eq43296 X1 X0
       grind)
    | exact resolve eq11 eq43296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43296
  have eq50588 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48970 X1 (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq48970
    | (have j0 := eq48970 X0 (τ X1)
       grind)
    | exact resolve eq48970 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq48970
  have eq50810 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50588 X0 X1
       have i₂ := eq4371 X1
       grind)
    | exact superpose eq4371 eq50588
    | (have j0 := eq50588 X0 X1
       grind)
    | exact resolve eq50588 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4371 eq50588
  have eq50907 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50810 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq50810
    | (have j0 := eq50810 X0 X1
       grind)
    | exact resolve eq50810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50810
  have eq50992 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50907 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq50907
    | (have j0 := eq50907 X0 X1
       grind)
    | exact resolve eq50907 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50907
  have eq51466 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq50992 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50992
  have eq54973 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49038 y x
       grind)
    | exact superpose eq49038 eq16
    | (have j1 := eq49038 y x
       grind)
    | exact resolve eq16 eq49038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49038
  have eq56305 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq54973
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq54973
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq54973 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54973
  have eq56308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq56305
  have eq56309 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq56308
  have eq56321 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51466 y x
       have i₂ := eq56309
       grind)
    | exact superpose eq56309 eq51466
    | (have j0 := eq51466 y x
       grind)
    | exact resolve eq51466 eq56309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51466
  have eq56322 : (τ x) ≠ (τ x) ∨ y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq56321
  have eq56323 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq56322
  have eq57848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5000 x
       have i₂ := eq56323
       grind)
    | exact superpose eq56323 eq5000
    | exact resolve eq5000 eq56323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56323
  have eq57890 : (σ y) = (σ (M.op x x)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq57848
       have r₂ := eq16
       grind)
    | exact resolve eq57848 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57848
  have eq57918 : (M.op x x) = (τ (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq57890
       grind)
    | exact superpose eq57890 eq10
    | exact resolve eq10 eq57890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57890
  have eq58084 : y = (M.op x x) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq57918
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq57918
    | exact resolve eq57918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57918
  have eq58748 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ x) = (τ (k y x)) := by
    first
    | (have i₁ := eq5000 x
       have i₂ := eq58084
       grind)
    | exact superpose eq58084 eq5000
    | exact resolve eq5000 eq58084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58084
  have eq58790 : (τ x) = (τ (k y x)) := by
    first
    | (have r₁ := eq58748
       have r₂ := eq16
       grind)
    | exact resolve eq58748 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58748
  have eq58807 : (k y x) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k y x)
       have i₂ := eq58790
       grind)
    | exact superpose eq58790 eq11
    | exact resolve eq11 eq58790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58790
  have eq59015 : x = (k y x) := by
    first
    | (have i₁ := eq58807
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq58807
    | exact resolve eq58807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58807
  have eq60416 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq31962 y x
       have i₂ := eq59015
       grind)
    | exact superpose eq59015 eq31962
    | (have j0 := eq31962 y x
       grind)
    | exact resolve eq31962 eq59015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31962 eq59015
  have eq60417 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq60416
  have eq65111 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60417
       grind)
    | exact superpose eq60417 eq16
    | exact resolve eq16 eq60417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60417
  have eq65168 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq65111
       have i₂ := eq56309
       grind)
    | exact superpose eq56309 eq65111
    | exact resolve eq65111 eq56309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56309 eq65111
  have eq65169 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq65168
  have eq65170 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq65169
  have eq65562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5000 x
       have i₂ := eq65170
       grind)
    | exact superpose eq65170 eq5000
    | exact resolve eq5000 eq65170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65170
  have eq65604 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq65562
       have r₂ := eq16
       grind)
    | exact resolve eq65562 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65562
  have eq65633 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq65604
       grind)
    | exact superpose eq65604 eq10
    | exact resolve eq10 eq65604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65604
  have eq65814 : y = (M.op x x) := by
    first
    | (have i₁ := eq65633
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq65633
    | exact resolve eq65633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65633
  have eq66434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5000 x
       have i₂ := eq65814
       grind)
    | exact superpose eq65814 eq5000
    | exact resolve eq5000 eq65814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5000 eq65814
  have eq66482 : False := by grind
  exact eq66482

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq91 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq15
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq91
    | exact resolve eq91 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq91
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq176 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq607 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | (have j0 := eq176 X1 (M.op X1 X1)
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq617 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq607 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq607
    | (have j0 := eq607 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq607 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq607
  have eq623 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq617 X0 X1
       have j1 := eq118 X1 X0
       grind)
    | (have r₁ := eq617 X0 X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq617 (σ (M.op X0 X0)) X0
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq617 (σ X0) (M.op X0 X0)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq617 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq617
  have eq626 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq623 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq623
    | exact resolve eq623 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq623 (σ X1) X0
       grind)
    | exact superpose eq623 eq15
    | (have j1 := eq623 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq666 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq626 (τ X0) X1
       grind)
    | exact superpose eq626 eq19
    | (have j1 := eq626 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq626
  have eq743 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq666 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666
    | exact resolve eq666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq788 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq743 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq743
    | (have j0 := eq743 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq743 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq948 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq637 x y
       grind)
    | exact superpose eq637 eq16
    | (have j1 := eq637 x y
       grind)
    | exact resolve eq16 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq963 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948
       have i₂ := eq788 x y
       grind)
    | exact superpose eq788 eq948
    | (have j1 := eq788 (σ x) (σ y)
       grind)
    | (have r₁ := eq948
       have r₂ := eq788 x y
       grind)
    | (have r₁ := eq948
       have r₂ := eq788 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq948
       have r₂ := eq788 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq948 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq948
  have eq964 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq963
  have eq967 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq16
    | exact resolve eq16 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq968 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq967
       have r₂ := eq102 x
       grind)
    | exact resolve eq967 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq969 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq968
       grind)
    | exact superpose eq968 eq16
    | exact resolve eq16 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq968
       grind)
    | exact superpose eq968 eq10
    | exact resolve eq10 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1015 : x = y := by
    first
    | (have i₁ := eq970
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq970
    | exact resolve eq970 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1016 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq969
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq969
    | exact resolve eq969 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq969
  have eq1017 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1016
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq1016
    | exact resolve eq1016 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq1016
  have eq1018 : False := by grind
  exact eq1018

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq149 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq658 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq734 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq149 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq149 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq149 (M.op (τ X1) X1) X1
       grind)
    | exact resolve eq13 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq744 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq734 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq745 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq744 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq2250 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq745
    | exact resolve eq745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq2302 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2250 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2250
    | (have j0 := eq2250 X0 X1
       grind)
    | exact resolve eq2250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250
  have eq2338 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2302 X1 X0
       grind)
    | exact superpose eq2302 eq10
    | (have j1 := eq2302 X1 X0
       grind)
    | exact resolve eq10 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2382 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2338 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2338
    | (have j0 := eq2338 X0 X1
       grind)
    | exact resolve eq2338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq2397 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq2382 X0 (σ X1)
       grind)
    | exact superpose eq2382 eq28
    | (have j1 := eq2382 X0 (σ X1)
       grind)
    | exact resolve eq28 eq2382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2382
  have eq4212 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq2397 (σ X0) X1
       grind)
    | exact superpose eq2397 eq37
    | (have j1 := eq2397 (σ X0) X1
       grind)
    | exact resolve eq37 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2397
  have eq4277 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4212 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4212
    | (have j0 := eq4212 X0 X1
       grind)
    | exact resolve eq4212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4212
  have eq4309 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4277 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4277
    | (have j0 := eq4277 X0 X1
       grind)
    | exact resolve eq4277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277
  have eq4319 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4309 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4309
    | (have j0 := eq4309 X0 X1
       grind)
    | exact resolve eq4309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309
  have eq4522 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4319 X0 X1
       grind)
    | exact superpose eq4319 eq11
    | (have j1 := eq4319 X0 X1
       grind)
    | exact resolve eq11 eq4319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4319
  have eq5394 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4522 x y
       grind)
    | exact superpose eq4522 eq16
    | (have j1 := eq4522 x y
       grind)
    | exact resolve eq16 eq4522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4522
  have eq5427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5394
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5394
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5394
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5394
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5394 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5428 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5394
       have i₂ := eq2302 y x
       grind)
    | exact superpose eq2302 eq5394
    | (have j1 := eq2302 y x
       grind)
    | (have r₁ := eq5394
       have r₂ := eq2302 y x
       grind)
    | (have r₁ := eq5394
       have r₂ := eq2302 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5394
       have r₂ := eq2302 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5394 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302 eq5394
  have eq5431 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5428
  have eq5432 : x = y ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq5431
  have eq5433 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5427
  have eq5434 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5433
  have eq5438 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5432
       grind)
    | exact superpose eq5432 eq16
    | exact resolve eq16 eq5432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5432
  have eq5439 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5438
       have r₂ := eq22 x
       grind)
    | exact resolve eq5438 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5438
  have eq5443 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq658 x y
       have i₂ := eq5439
       grind)
    | exact superpose eq5439 eq658
    | (have j0 := eq658 x y
       grind)
    | exact resolve eq658 eq5439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq5439
  have eq5450 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5443
  have eq5451 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5450
  have eq5463 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5451
       grind)
    | exact superpose eq5451 eq16
    | exact resolve eq16 eq5451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5451
  have eq5479 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5463
       have i₂ := eq5434
       grind)
    | exact superpose eq5434 eq5463
    | exact resolve eq5463 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5434 eq5463
  have eq5480 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5479
  have eq5481 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5480
  have eq5482 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5481
       grind)
    | exact superpose eq5481 eq16
    | exact resolve eq16 eq5481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5481
  have eq5483 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5482
       have r₂ := eq22 x
       grind)
    | exact resolve eq5482 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482
  have eq5484 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5483
       grind)
    | exact superpose eq5483 eq16
    | exact resolve eq16 eq5483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5485 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5483
       grind)
    | exact superpose eq5483 eq10
    | exact resolve eq10 eq5483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5483
  have eq5540 : x = y := by
    first
    | (have i₁ := eq5485
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5485
    | exact resolve eq5485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5485
  have eq5541 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5484
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5484
    | exact resolve eq5484 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5484
  have eq5542 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5541
       have i₂ := eq5540
       grind)
    | exact superpose eq5540 eq5541
    | exact resolve eq5541 eq5540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5540 eq5541
  have eq5543 : False := by grind
  exact eq5543

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq444 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq469 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq478 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq461
    | (have j0 := eq461 X0 X1
       grind)
    | exact resolve eq461 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq668 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq478 x y
       grind)
    | exact superpose eq478 eq16
    | (have j1 := eq478 x y
       grind)
    | exact resolve eq16 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq478 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq3709 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq469
    | exact resolve eq469 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq3771 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3709 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3709
    | (have j0 := eq3709 X0 X1
       grind)
    | exact resolve eq3709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709
  have eq7163 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq668
       have i₂ := eq3771 y x
       grind)
    | exact superpose eq3771 eq668
    | (have j1 := eq3771 y x
       grind)
    | (have r₁ := eq668
       have r₂ := eq3771 y x
       grind)
    | (have r₁ := eq668
       have r₂ := eq3771 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq668
       have r₂ := eq3771 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq668 eq3771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq3771
  have eq7164 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq7163
  have eq7182 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq674 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq674
    | (have j0 := eq674 (τ X1) (τ X0)
       grind)
    | exact resolve eq674 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq7240 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7182 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7182
    | (have j0 := eq7182 X0 X1
       grind)
    | exact resolve eq7182 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182
  have eq7275 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7240 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7240
    | (have j0 := eq7240 X0 X1
       grind)
    | exact resolve eq7240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7240
  have eq7307 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7275 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7275
    | (have j0 := eq7275 X0 X1
       grind)
    | exact resolve eq7275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7275
  have eq7333 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7307 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7307
    | (have j0 := eq7307 X0 X1
       grind)
    | exact resolve eq7307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7307
  have eq7353 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7333 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7333
    | (have j0 := eq7333 X0 X1
       grind)
    | exact resolve eq7333 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7333
  have eq7372 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7353 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7353
    | (have j0 := eq7353 X0 X1
       grind)
    | exact resolve eq7353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7353
  have eq7385 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7372 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7372
    | (have j0 := eq7372 X0 X1
       grind)
    | exact resolve eq7372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7372
  have eq16378 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq7164
       grind)
    | exact superpose eq7164 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7164
       grind)
    | exact resolve eq13 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7164
  have eq16379 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16378
  have eq16380 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16379
  have eq16553 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16380
       grind)
    | exact superpose eq16380 eq16
    | exact resolve eq16 eq16380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16380
  have eq16554 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq16553
       have r₂ := eq22 x
       grind)
    | exact resolve eq16553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16553
  have eq16557 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq444 x (σ y)
       have i₂ := eq16554
       grind)
    | exact superpose eq16554 eq444
    | (have j0 := eq444 x (σ y)
       grind)
    | (have r₁ := eq444 x (σ y)
       have r₂ := eq16554
       grind)
    | exact resolve eq444 eq16554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16554
  have eq16564 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq16557
  have eq16565 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq16564
  have eq16568 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16565
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16565
    | exact resolve eq16565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16565
  have eq16577 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq674 x y
       have i₂ := eq16568
       grind)
    | exact superpose eq16568 eq674
    | (have j0 := eq674 x y
       grind)
    | (have r₁ := eq674 x y
       have r₂ := eq16568
       grind)
    | exact resolve eq674 eq16568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16568
  have eq16599 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq16577
  have eq16600 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq16599
  have eq16604 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq674 x y
       grind)
    | (have r₁ := eq16600
       have r₂ := eq674 x y
       grind)
    | exact resolve eq16600 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq16600
  have eq16607 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16604
       grind)
    | exact superpose eq16604 eq16
    | exact resolve eq16 eq16604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16608 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq444 x (σ y)
       have i₂ := eq16604
       grind)
    | exact superpose eq16604 eq444
    | (have j0 := eq444 x (σ y)
       grind)
    | (have r₁ := eq444 x (σ y)
       have r₂ := eq16604
       grind)
    | exact resolve eq444 eq16604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq16604
  have eq16615 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq16608
  have eq16616 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq16615
  have eq16619 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16616
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16616
    | exact resolve eq16616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16616
  have eq16626 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq16619
       grind)
    | exact superpose eq16619 eq10
    | exact resolve eq10 eq16619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16619
  have eq16805 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16626
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16626
    | exact resolve eq16626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16626
  have eq16807 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16805
       grind)
    | exact superpose eq16805 eq16
    | exact resolve eq16 eq16805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16805
  have eq16808 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq16807
       have r₂ := eq22 x
       grind)
    | exact resolve eq16807 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16807
  have eq16818 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq16808
       grind)
    | exact superpose eq16808 eq10
    | exact resolve eq10 eq16808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16808
  have eq16998 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq16818
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq16818
    | exact resolve eq16818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16818
  have eq17022 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7385 y x
       have i₂ := eq16998
       grind)
    | exact superpose eq16998 eq7385
    | (have j0 := eq7385 y x
       grind)
    | (have r₁ := eq7385 y x
       have r₂ := eq16998
       grind)
    | exact resolve eq7385 eq16998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7385 eq16998
  have eq17025 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17022
  have eq17029 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16607
       have i₂ := eq17025
       grind)
    | exact superpose eq17025 eq16607
    | exact resolve eq16607 eq17025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16607 eq17025
  have eq17035 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq17029
  have eq17036 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17035
       grind)
    | exact superpose eq17035 eq16
    | exact resolve eq16 eq17035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17035
  have eq17039 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq17036
       have r₂ := eq22 x
       grind)
    | exact resolve eq17036 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17036
  have eq17040 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17039
       grind)
    | exact superpose eq17039 eq16
    | exact resolve eq16 eq17039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17041 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq17039
       grind)
    | exact superpose eq17039 eq10
    | exact resolve eq10 eq17039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17039
  have eq17220 : x = y := by
    first
    | (have i₁ := eq17041
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17041
    | exact resolve eq17041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17041
  have eq17221 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17040
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq17040
    | exact resolve eq17040 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17040
  have eq17222 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq17221
       have i₂ := eq17220
       grind)
    | exact superpose eq17220 eq17221
    | exact resolve eq17221 eq17220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220 eq17221
  have eq17223 : False := by grind
  exact eq17223

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  clear eq17
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X0))) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq92 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op X1 (M.op (σ X0) (M.op X1 (σ X0)))) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq61
    | exact resolve eq61 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq452 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq479 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq456
    | (have j0 := eq456 X0 X1
       grind)
    | exact resolve eq456 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq723 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq3554 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq452 X0 X1
       grind)
    | exact superpose eq452 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq452 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq452 X0 X1
       grind)
    | exact resolve eq13 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3576 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq452 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq3577 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3554 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq3596 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3577 X0 X1
       have j1 := eq3576 X0 X1
       grind)
    | (have r₁ := eq3577 X0 X1
       have r₂ := eq3576 X0 X1
       grind)
    | exact resolve eq3577 eq3576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3576 eq3577
  have eq3882 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3596 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3596
    | exact resolve eq3596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3907 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq3596 X0 X1
       grind)
    | exact superpose eq3596 eq22
    | (have j1 := eq3596 X0 X1
       grind)
    | exact resolve eq22 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3920 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq3596 (σ X0) X1
       grind)
    | exact superpose eq3596 eq28
    | (have j1 := eq3596 (σ X0) X1
       grind)
    | exact resolve eq28 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3596
  have eq3969 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3920 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3920
    | (have j0 := eq3920 X0 X1
       grind)
    | exact resolve eq3920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920
  have eq3979 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3882 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq3882
    | (have j0 := eq3882 X0 X1
       grind)
    | exact resolve eq3882 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3882
  have eq4000 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3969 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3969
    | (have j0 := eq3969 X0 X1
       grind)
    | exact resolve eq3969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3969
  have eq4027 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4000 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4000
    | (have j0 := eq4000 X0 X1
       grind)
    | exact resolve eq4000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq4033 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4027 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq4027
    | (have j0 := eq4027 X0 X1
       grind)
    | exact resolve eq4027 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4027
  have eq4066 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq3979 X1 X0
       grind)
    | exact superpose eq3979 eq11
    | (have j1 := eq3979 X1 X0
       grind)
    | exact resolve eq11 eq3979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3979
  have eq4184 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4066 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4066
    | (have j0 := eq4066 X0 X1
       grind)
    | exact resolve eq4066 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066
  have eq4225 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq4184 X0 (τ X1)
       grind)
    | exact superpose eq4184 eq18
    | (have j1 := eq4184 X0 (τ X1)
       grind)
    | exact resolve eq18 eq4184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4377 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4225 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4225
    | exact resolve eq4225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4225
  have eq4443 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4377 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4377
    | (have j0 := eq4377 X0 X1
       grind)
    | exact resolve eq4377 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4377
  have eq13280 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3907 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3907
    | (have j0 := eq3907 X1 (τ X0)
       grind)
    | exact resolve eq3907 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907
  have eq13415 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13280 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq13280
    | (have j0 := eq13280 X0 X1
       grind)
    | exact resolve eq13280 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13280
  have eq13422 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13415 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq13415
    | (have j0 := eq13415 X0 X1
       grind)
    | exact resolve eq13415 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13415
  have eq13497 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq13422 X1 X0
       grind)
    | exact superpose eq13422 eq11
    | (have j1 := eq13422 X1 X0
       grind)
    | exact resolve eq11 eq13422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13422
  have eq13621 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13497 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq13497
    | (have j0 := eq13497 X0 X1
       grind)
    | exact resolve eq13497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13497
  have eq13811 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13621 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13621
    | (have j0 := eq13621 (σ X0) (σ X1)
       grind)
    | exact resolve eq13621 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13621
  have eq14050 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13811 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq13811
    | (have j0 := eq13811 X0 X1
       grind)
    | exact resolve eq13811 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13811
  have eq14078 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14050 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14050
    | (have j0 := eq14050 X0 X1
       grind)
    | exact resolve eq14050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14050
  have eq14094 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14078 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq14078
    | (have j0 := eq14078 X0 X1
       grind)
    | exact resolve eq14078 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14078
  have eq23057 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14094 x y
       grind)
    | exact superpose eq14094 eq16
    | (have j1 := eq14094 x y
       grind)
    | exact resolve eq16 eq14094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14094
  have eq23210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq23057
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq23057
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq23057 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23211 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq23057
       have i₂ := eq4443 y x
       grind)
    | exact superpose eq4443 eq23057
    | (have j1 := eq4443 y x
       grind)
    | (have r₁ := eq23057
       have r₂ := eq4443 y x
       grind)
    | exact resolve eq23057 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443 eq23057
  have eq23214 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq23211
  have eq23215 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by grind
  clear eq23214
  have eq23216 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq23210
  have eq23217 : x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq23216
  have eq23231 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq23215
       grind)
    | exact superpose eq23215 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq23215
       grind)
    | exact resolve eq12 eq23215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23215
  have eq23236 : x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq23231
  have eq23257 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq724 x y
       have i₂ := eq23236
       grind)
    | exact superpose eq23236 eq724
    | (have j0 := eq724 x y
       grind)
    | exact resolve eq724 eq23236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq23236
  have eq23270 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq23257
  have eq23271 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq23270
  have eq28754 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23271
       grind)
    | exact superpose eq23271 eq16
    | exact resolve eq16 eq23271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23271
  have eq28793 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq28754
       have i₂ := eq23217
       grind)
    | exact superpose eq23217 eq28754
    | exact resolve eq28754 eq23217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23217 eq28754
  have eq28816 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq28793
  have eq28817 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq28816
  have eq28829 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq28817
       have r₂ := eq12 x y
       grind)
    | exact resolve eq28817 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28817
  have eq28846 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq92 x (σ y)
       have i₂ := eq28829
       grind)
    | exact superpose eq28829 eq92
    | (have j0 := eq92 x (σ y)
       grind)
    | (have r₁ := eq92 x (σ y)
       have r₂ := eq28829
       grind)
    | exact resolve eq92 eq28829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq28829
  have eq28869 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by grind
  clear eq28846
  have eq28875 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28869
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq28869
    | exact resolve eq28869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28869
  have eq28931 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq28875
       have i₂ := eq4184 x y
       grind)
    | exact superpose eq4184 eq28875
    | (have j1 := eq4184 x y
       grind)
    | exact resolve eq28875 eq4184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4184
  have eq28932 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq28875
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq28875
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq28875 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28936 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq723 x y
       have i₂ := eq28875
       grind)
    | exact superpose eq28875 eq723
    | (have j0 := eq723 x y
       grind)
    | (have r₁ := eq723 x y
       have r₂ := eq28875
       grind)
    | exact resolve eq723 eq28875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29001 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq28936
  have eq29003 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq28932
  have eq29004 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (k x y) := by grind
  clear eq28931
  have eq29006 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq723 x y
       grind)
    | (have r₁ := eq29001
       have r₂ := eq723 x y
       grind)
    | exact resolve eq29001 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq29001
  have eq29014 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4033 x y
       have i₂ := eq29006
       grind)
    | exact superpose eq29006 eq4033
    | (have j0 := eq4033 x y
       grind)
    | exact resolve eq4033 eq29006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4033
  have eq29029 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq29006
  have eq29043 : (k x y) = (τ (σ x)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq29014
       have r₂ := eq29029
       grind)
    | exact resolve eq29014 eq29029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29014
  have eq29051 : x = (k x y) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq29043
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29043
    | exact resolve eq29043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29043
  have eq29052 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by grind
  clear eq29051
  have eq29073 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29052
       grind)
    | exact superpose eq29052 eq16
    | exact resolve eq16 eq29052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29052
  have eq31845 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq29073
       have i₂ := eq29004
       grind)
    | exact superpose eq29004 eq29073
    | (have r₁ := eq29073
       have r₂ := eq29004
       grind)
    | exact resolve eq29073 eq29004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29004
  have eq31856 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq31845
  have eq31857 : x = (k x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq31856
  have eq31868 : x = (k x y) := by
    first
    | (have r₁ := eq31857
       have r₂ := eq29073
       grind)
    | exact resolve eq31857 eq29073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29073 eq31857
  have eq31882 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28875
       have i₂ := eq31868
       grind)
    | exact superpose eq31868 eq28875
    | exact resolve eq28875 eq31868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28875 eq31868
  have eq31970 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) (σ x)) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq109 x X0
       have i₂ := eq31882
       grind)
    | exact superpose eq31882 eq109
    | exact resolve eq109 eq31882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq31882
  have eq32052 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq31970 x
       have i₂ := eq9 (σ x) x
       grind)
    | exact superpose eq9 eq31970
    | exact resolve eq31970 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31970
  have eq32067 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq32052
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq32052
    | exact resolve eq32052 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq32052
  have eq32068 : (σ x) = (σ (M.op x x)) := by grind
  clear eq32067
  have eq32073 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29029
       have i₂ := eq32068
       grind)
    | exact superpose eq32068 eq29029
    | (have r₁ := eq29029
       have r₂ := eq32068
       grind)
    | exact resolve eq29029 eq32068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29029
  have eq32082 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq32068
       grind)
    | exact superpose eq32068 eq10
    | exact resolve eq10 eq32068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32189 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32073
  have eq32263 : x = (M.op x x) := by
    first
    | (have i₁ := eq32082
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq32082
    | exact resolve eq32082 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32082
  have eq32481 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32189
       grind)
    | exact superpose eq32189 eq16
    | exact resolve eq16 eq32189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32189
  have eq32530 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq32481
       have i₂ := eq29003
       grind)
    | exact superpose eq29003 eq32481
    | exact resolve eq32481 eq29003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29003
  have eq32554 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq32530
  have eq32567 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq32554
       have i₂ := eq32068
       grind)
    | exact superpose eq32068 eq32554
    | exact resolve eq32554 eq32068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32068 eq32554
  have eq32578 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq32567
       have r₂ := eq32481
       grind)
    | exact resolve eq32567 eq32481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32567
  have eq32579 : x = (M.op x y) := by
    first
    | (have i₁ := eq32578
       have i₂ := eq32263
       grind)
    | exact superpose eq32263 eq32578
    | exact resolve eq32578 eq32263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32263 eq32578
  have eq32598 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq32481
       have i₂ := eq32579
       grind)
    | exact superpose eq32579 eq32481
    | exact resolve eq32481 eq32579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32481 eq32579
  have eq32610 : False := by grind
  exact eq32610

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_y_pyx_y_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq70 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2956 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq74 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2957 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq2956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956
  have eq2960 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2957 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2957
    | (have j0 := eq2957 X0
       grind)
    | exact resolve eq2957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2957
  have eq2965 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2960 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2960
    | exact resolve eq2960 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960
  have eq2997 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2965 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq2965
    | (have j0 := eq2965 X0
       grind)
    | exact resolve eq2965 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2965
  have eq2999 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq2997 X0
       grind)
    | exact superpose eq2997 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq2997 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2997 X0
       grind)
    | exact resolve eq12 eq2997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq3007 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2999 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq3015 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq3050 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3015 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3015
    | (have j0 := eq3015 X0 X0
       grind)
    | exact resolve eq3015 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015
  have eq3067 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3007 X0 X1
       grind)
    | exact superpose eq3007 eq11
    | (have j1 := eq3007 X0 X1
       grind)
    | exact resolve eq11 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3156 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3067 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3067
    | (have j0 := eq3067 X0 X0
       grind)
    | exact resolve eq3067 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3067
  have eq3239 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3156 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3240 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq3442 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3240 (σ X0)
       grind)
    | exact superpose eq3240 eq15
    | exact resolve eq15 eq3240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3450 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq3240 (τ X0)
       grind)
    | exact superpose eq3240 eq32
    | exact resolve eq32 eq3240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3501 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3450 X0
       have i₂ := eq3240 X0
       grind)
    | exact superpose eq3240 eq3450
    | exact resolve eq3450 eq3240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3450
  have eq3508 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3442 X0
       have i₂ := eq3240 X0
       grind)
    | exact superpose eq3240 eq3442
    | exact resolve eq3442 eq3240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3240 eq3442
  have eq4671 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (τ (k X0 X2)) = (τ (M.op X2 X0)) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq3050 X0 X2
       grind)
    | exact superpose eq3050 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq3050 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3050 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq3050 X0 X0
       grind)
    | exact resolve eq12 eq3050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3050
  have eq4698 : ∀ X0 X1 X2 : G, (τ (k X0 X2)) = (τ (M.op X2 X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq4671 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq9752 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq4698 X1 X2 X0
       grind)
    | exact superpose eq4698 eq11
    | (have j1 := eq4698 X1 X2 X0
       grind)
    | exact resolve eq11 eq4698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4698
  have eq9876 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9752 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq9752
    | (have j0 := eq9752 X0 X1 X0
       grind)
    | exact resolve eq9752 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9752
  have eq10038 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9876 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9876
  have eq10039 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10038 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10038
  have eq10233 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq10039 (σ X1) (σ X0)
       grind)
    | exact superpose eq10039 eq15
    | (have j1 := eq10039 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq10039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10246 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq10039 (τ X1) X0
       grind)
    | exact superpose eq10039 eq17
    | (have j1 := eq10039 (τ X1) X0
       grind)
    | exact resolve eq17 eq10039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq10039
  have eq10787 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10246 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10246
    | exact resolve eq10246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10246
  have eq10929 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10787 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10787
    | (have j0 := eq10787 X0 X1
       grind)
    | exact resolve eq10787 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10787
  have eq11045 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10929 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq10929
    | (have j0 := eq10929 (τ X0) (τ X1)
       grind)
    | exact resolve eq10929 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10929
  have eq11196 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11045 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11045
    | (have j0 := eq11045 X0 X1
       grind)
    | exact resolve eq11045 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11045
  have eq11619 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10233 x y
       grind)
    | exact superpose eq10233 eq16
    | (have j1 := eq10233 x y
       grind)
    | exact resolve eq16 eq10233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11694 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10233
  have eq12078 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11694 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq11694
    | (have j0 := eq11694 (τ X1) (τ X0)
       grind)
    | exact resolve eq11694 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12133 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12078 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq12078
    | (have j0 := eq12078 X0 X1
       grind)
    | exact resolve eq12078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12078
  have eq12159 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12133 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12133
    | (have j0 := eq12133 X0 X1
       grind)
    | exact resolve eq12133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12133
  have eq12180 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12159 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12159
    | (have j0 := eq12159 X0 X1
       grind)
    | exact resolve eq12159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12159
  have eq12195 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12180 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12180
    | (have j0 := eq12180 X0 X1
       grind)
    | exact resolve eq12180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12180
  have eq15672 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq11196 X1 X0
       grind)
    | exact superpose eq11196 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq11196 X1 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq11196 X0 X1
       grind)
    | exact resolve eq13 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11196
  have eq15682 : ∀ X0 X1 : G, (τ X0) = (k (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq15672 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15672
  have eq15700 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15682 X0 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq15682
    | (have j0 := eq15682 X0 X1
       grind)
    | exact resolve eq15682 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq15682
  have eq15737 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15700 X0 X1
       have i₂ := eq3501 X1
       grind)
    | exact superpose eq3501 eq15700
    | (have j0 := eq15700 X0 X1
       grind)
    | exact resolve eq15700 eq3501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3501 eq15700
  have eq539700 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (τ X1) = (τ (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15737 X1 (σ X0)
       have i₂ := eq3508 X0
       grind)
    | exact superpose eq3508 eq15737
    | (have j0 := eq15737 X1 (σ X0)
       grind)
    | exact resolve eq15737 eq3508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508 eq15737
  have eq540435 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (τ X1) = (τ (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq539700 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq539700
    | (have j0 := eq539700 X0 X1
       grind)
    | exact resolve eq539700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539700
  have eq540468 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ X1) = (τ (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq540435 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq540435
    | (have j0 := eq540435 X0 X1
       grind)
    | exact resolve eq540435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540435
  have eq540492 : ∀ X0 X1 : G, (τ X1) = (k X0 (τ X1)) ∨ (M.op X0 X0) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq540468 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq540468
    | (have j0 := eq540468 X0 X1
       grind)
    | exact resolve eq540468 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540468
  have eq540506 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (k X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq540492 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq540492
    | (have j0 := eq540492 X0 X1
       grind)
    | exact resolve eq540492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540492
  have eq544145 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = (k X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq540506 X0 X1
       grind)
    | exact superpose eq540506 eq10
    | (have j1 := eq540506 X0 X1
       grind)
    | exact resolve eq10 eq540506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540506
  have eq544583 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = (k X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq544145 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq544145
    | (have j0 := eq544145 X0 X1
       grind)
    | exact resolve eq544145 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq544145
  have eq544704 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq544583 X0 X1
       have j1 := eq12 X0 (τ X1)
       grind)
    | (have r₁ := eq544583 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq544583 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544583
  have eq547451 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq544704 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq544704
    | exact resolve eq544704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544704
  have eq549671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11619
       have i₂ := eq547451 x y
       grind)
    | exact superpose eq547451 eq11619
    | (have j1 := eq547451 x y
       grind)
    | exact resolve eq11619 eq547451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11619
  have eq549676 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq547451 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547451
  have eq549678 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq549671
  have eq553531 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq549676 (σ y) (σ x)
       have i₂ := eq549678
       grind)
    | exact superpose eq549678 eq549676
    | (have j0 := eq549676 (σ y) (σ x)
       grind)
    | (have r₁ := eq549676 (σ y) (σ x)
       have r₂ := eq549678
       grind)
    | exact resolve eq549676 eq549678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549678
  have eq553532 : (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by grind
  clear eq553531
  have eq553534 : x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq553532
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq553532
    | exact resolve eq553532 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553532
  have eq556282 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11694 x y
       have i₂ := eq553534
       grind)
    | exact superpose eq553534 eq11694
    | (have j0 := eq11694 x y
       grind)
    | (have r₁ := eq11694 x y
       have r₂ := eq553534
       grind)
    | exact resolve eq11694 eq553534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553534
  have eq556404 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq556282
  have eq556416 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq11694 x y
       grind)
    | (have r₁ := eq556404
       have r₂ := eq11694 x y
       grind)
    | exact resolve eq556404 eq11694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11694 eq556404
  have eq558910 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq556416
       grind)
    | exact superpose eq556416 eq16
    | exact resolve eq16 eq556416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558980 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq549676 (σ y) (σ x)
       have i₂ := eq556416
       grind)
    | exact superpose eq556416 eq549676
    | (have j0 := eq549676 (σ y) (σ x)
       grind)
    | (have r₁ := eq549676 (σ y) (σ x)
       have r₂ := eq556416
       grind)
    | exact resolve eq549676 eq556416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549676 eq556416
  have eq558981 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq558980
  have eq558983 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq558981
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq558981
    | exact resolve eq558981 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558981
  have eq562072 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq558983
       grind)
    | exact superpose eq558983 eq10
    | exact resolve eq10 eq558983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558983
  have eq562599 : x = (k y x) := by
    first
    | (have i₁ := eq562072
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq562072
    | exact resolve eq562072 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562072
  have eq562832 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12195 y x
       have i₂ := eq562599
       grind)
    | exact superpose eq562599 eq12195
    | (have j0 := eq12195 y x
       grind)
    | (have r₁ := eq12195 y x
       have r₂ := eq562599
       grind)
    | exact resolve eq12195 eq562599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195 eq562599
  have eq562950 : x = (M.op x y) := by grind
  clear eq562832
  have eq565881 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq558910
       have i₂ := eq562950
       grind)
    | exact superpose eq562950 eq558910
    | exact resolve eq558910 eq562950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558910 eq562950
  have eq565931 : False := by grind
  exact eq565931
