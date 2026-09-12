import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X0)) X1) := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq96 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
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
  have eq108 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (k (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 X1))
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (M.op X1 (M.op X0 X1)) (M.op X0 (M.op X1 X1))
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq110 X0 X0
       grind)
    | (have r₁ := eq109 x
       have r₂ := eq110 x x
       grind)
    | exact resolve eq109 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq110
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq115
    | exact resolve eq115 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq376 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (M.op X0 X0) X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 X0)
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq62
    | (have j1 := eq108 X0
       grind)
    | exact resolve eq62 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq108
  have eq658 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq16
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq888 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq376 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq376
    | (have j0 := eq376 X0
       have j1 := eq65 X0
       grind)
    | exact resolve eq376 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq376
  have eq893 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq903 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq893 X0
       grind)
    | exact superpose eq893 eq116
    | (have j1 := eq893 X0
       grind)
    | exact resolve eq116 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq893
  have eq908 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq903 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq926 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq908 (σ X0)
       grind)
    | exact superpose eq908 eq15
    | exact resolve eq15 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq926 X0
       have i₂ := eq908 X0
       grind)
    | exact superpose eq908 eq926
    | exact resolve eq926 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq926
  have eq2768 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq2827 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2768 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2768
    | (have j0 := eq2768 X0 X1
       grind)
    | exact resolve eq2768 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq14101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq658
       have i₂ := eq2827 x y
       grind)
    | exact superpose eq2827 eq658
    | (have j1 := eq2827 (σ x) (σ y)
       grind)
    | (have r₁ := eq658
       have r₂ := eq2827 x y
       grind)
    | (have r₁ := eq658
       have r₂ := eq2827 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq658
       have r₂ := eq2827 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq658 eq2827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14102 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq14101
  have eq14104 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14102
       grind)
    | exact superpose eq14102 eq16
    | exact resolve eq16 eq14102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14102
  have eq14105 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq14104
       have r₂ := eq945 x
       grind)
    | exact resolve eq14104 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14104
  have eq14107 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14105
       grind)
    | exact superpose eq14105 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14105
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14105
       grind)
    | exact resolve eq12 eq14105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14105
  have eq14111 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq14107
  have eq14112 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq658
       have i₂ := eq14111
       grind)
    | exact superpose eq14111 eq658
    | exact resolve eq658 eq14111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq14111
  have eq14113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq14112
  have eq14114 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq14113
  have eq14120 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq14114
       grind)
    | exact superpose eq14114 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14114
       grind)
    | exact resolve eq12 eq14114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14114
  have eq14124 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq14120
  have eq14130 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14124
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14124
    | exact resolve eq14124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14124
  have eq14144 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14130
       grind)
    | exact superpose eq14130 eq16
    | exact resolve eq16 eq14130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14130
  have eq14205 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14144
       have i₂ := eq2827 x y
       grind)
    | exact superpose eq2827 eq14144
    | (have j1 := eq2827 x y
       grind)
    | (have r₁ := eq14144
       have r₂ := eq2827 x y
       grind)
    | (have r₁ := eq14144
       have r₂ := eq2827 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq14144
       have r₂ := eq2827 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq14144 eq2827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827
  have eq14206 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq14205
  have eq14210 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14206
       grind)
    | exact superpose eq14206 eq16
    | exact resolve eq16 eq14206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14206
  have eq14211 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14210
       have r₂ := eq945 x
       grind)
    | exact resolve eq14210 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14210
  have eq14213 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14211
       grind)
    | exact superpose eq14211 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14211
       grind)
    | exact resolve eq12 eq14211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14211
  have eq14217 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq14213
  have eq14218 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14144
       have i₂ := eq14217
       grind)
    | exact superpose eq14217 eq14144
    | exact resolve eq14144 eq14217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14144 eq14217
  have eq14222 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq14218
  have eq14223 : (σ x) = (σ y) := by grind
  clear eq14222
  have eq14224 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14223
       grind)
    | exact superpose eq14223 eq16
    | exact resolve eq16 eq14223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14225 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14223
       grind)
    | exact superpose eq14223 eq10
    | exact resolve eq10 eq14223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14223
  have eq14286 : x = y := by
    first
    | (have i₁ := eq14225
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14225
    | exact resolve eq14225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14225
  have eq14287 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14224
       have i₂ := eq945 x
       grind)
    | exact superpose eq945 eq14224
    | exact resolve eq14224 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq14224
  have eq14292 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14287
       have i₂ := eq14286
       grind)
    | exact superpose eq14286 eq14287
    | exact resolve eq14287 eq14286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14286 eq14287
  have eq14293 : False := by grind
  exact eq14293

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq22
  have eq277 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq277 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq280 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq278 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq278 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq278 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq293 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq280 (σ X0)
       grind)
    | exact superpose eq280 eq15
    | exact resolve eq15 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq280 (τ X0)
       grind)
    | exact superpose eq280 eq31
    | exact resolve eq31 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq306 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq299
    | exact resolve eq299 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq312 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq293 X0
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq293
    | exact resolve eq293 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq293
  have eq358 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq361 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq358 X0 X1
       have j1 := eq360 X0 X1
       grind)
    | (have r₁ := eq358 X0 X1
       have r₂ := eq360 X0 X1
       grind)
    | exact resolve eq358 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq360
  have eq375 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq378 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq375 X0 X1
       have j1 := eq377 X0 X1
       grind)
    | (have r₁ := eq375 X0 X1
       have r₂ := eq377 X0 X1
       grind)
    | exact resolve eq375 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq377
  have eq402 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq361 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq361
    | exact resolve eq361 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq361 x (σ y)
       grind)
    | exact superpose eq361 eq16
    | (have j1 := eq361 x (σ y)
       grind)
    | exact resolve eq16 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq361 X1 X0
       grind)
    | exact superpose eq361 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq361 X1 (σ X1)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq361 X0 X1
       grind)
    | exact resolve eq13 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq419 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq410 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq423 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq419 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq419 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq419 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq426 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq406
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq406
    | exact resolve eq406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq434 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq402 X1 X0
       grind)
    | exact superpose eq402 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq402 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq402 X0 X1
       grind)
    | exact resolve eq13 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq450 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq434 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq456 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq450 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq450 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq450 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq470 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq456 X1 (τ X0)
       grind)
    | exact superpose eq456 eq18
    | (have j1 := eq456 X1 (τ X0)
       grind)
    | exact resolve eq18 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq487 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq456 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq794 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq470 X1 (τ X0)
       grind)
    | exact superpose eq470 eq17
    | (have j1 := eq470 X1 (τ X0)
       grind)
    | exact resolve eq17 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq470
  have eq801 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq794 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq794
    | (have j0 := eq794 X0 X1
       grind)
    | exact resolve eq794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq812 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq801 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq801
    | (have j0 := eq801 X0 X1
       grind)
    | exact resolve eq801 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq813 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq812 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq812
    | (have j0 := eq812 X0 X1
       grind)
    | exact resolve eq812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq870 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq813 X0 (σ X1)
       have i₂ := eq423 X0 X1
       grind)
    | exact superpose eq423 eq813
    | (have j0 := eq813 X1 (σ X0)
       have j1 := eq423 X1 X0
       grind)
    | exact resolve eq813 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq813
  have eq934 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq870 X0 X1
       have j1 := eq487 X1 (σ X0)
       grind)
    | (have r₁ := eq870 X0 X0
       have r₂ := eq487 X0 (σ X0)
       grind)
    | exact resolve eq870 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq870
  have eq955 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq934
    | (have j0 := eq934 X0 X1
       grind)
    | exact resolve eq934 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1501 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq955 X1 (σ X0)
       grind)
    | exact superpose eq955 eq28
    | (have j1 := eq955 X1 (σ X0)
       grind)
    | exact resolve eq28 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq955
  have eq1512 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1501 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1501
    | (have j0 := eq1501 X0 X1
       grind)
    | exact resolve eq1501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1525 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1512 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1512
    | (have j0 := eq1512 X0 X1
       grind)
    | exact resolve eq1512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1534 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1525 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1525
    | (have j0 := eq1525 X0 X1
       grind)
    | exact resolve eq1525 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525
  have eq1539 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1534 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1534
    | (have j0 := eq1534 X1 (τ X0)
       grind)
    | exact resolve eq1534 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1560 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1534 y x
       grind)
    | exact superpose eq1534 eq16
    | (have j1 := eq1534 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1534 y x
       grind)
    | exact resolve eq16 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1582 : y = (k y x) := by grind
  clear eq1560
  have eq1779 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X1 X0
       have i₂ := eq1539 X1 X0
       grind)
    | exact superpose eq1539 eq378
    | (have j0 := eq378 X1 X0
       have j1 := eq1539 X1 X0
       grind)
    | exact resolve eq378 eq1539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq1539
  have eq1792 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1779 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1809 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1792 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1792
    | exact resolve eq1792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1919 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1809 x y
       grind)
    | exact superpose eq1809 eq16
    | (have j1 := eq1809 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1809 x y
       grind)
    | exact resolve eq16 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1942 : y = (M.op x y) := by grind
  clear eq1919
  have eq2076 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq426
       have i₂ := eq1942
       grind)
    | exact superpose eq1942 eq426
    | exact resolve eq426 eq1942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq2081 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq2076
  have eq2084 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2081
       have i₂ := eq1582
       grind)
    | exact superpose eq1582 eq2081
    | exact resolve eq2081 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582 eq2081
  have eq2089 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2084
       grind)
    | exact superpose eq2084 eq16
    | exact resolve eq16 eq2084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2111 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2089
       have i₂ := eq1942
       grind)
    | exact superpose eq1942 eq2089
    | exact resolve eq2089 eq1942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942 eq2089
  have eq2112 : False := by grind
  exact eq2112

/-- `Equation3871`: `x ◇ x = (x ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_y_pxy_Equation3871 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3871 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3871.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
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
  clear eq19
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X1) = (M.op (M.op X0 (M.op X2 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X2 (M.op (M.op X0 (M.op X1 X1)) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X1) ≠ X0 ∨ (M.op (M.op X0 (M.op X1 X1)) X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq9 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X1)) ∨ (k X1 (M.op X0 (M.op X1 X1))) = (M.op X1 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op X1 X1))
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq9 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq14 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq197 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq197
    | (have j0 := eq197 (σ X0) (σ X1)
       grind)
    | exact resolve eq197 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (σ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq197 (σ X0) X1
       grind)
    | exact superpose eq197 eq29
    | (have j1 := eq197 (σ X0) X1
       grind)
    | exact resolve eq29 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op (σ X0) (M.op X1 X1)) X1) ∨ (σ X0) = (M.op (M.op (σ X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X0
       have i₂ := eq9 (σ X0) X1
       grind)
    | exact superpose eq9 eq198
    | exact resolve eq198 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198 x y
       grind)
    | exact superpose eq198 eq16
    | (have j1 := eq198 x y
       grind)
    | exact resolve eq16 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq616 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq370
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq370
    | (have j1 := eq197 (σ x) (σ y)
       grind)
    | exact resolve eq370 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq619 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq616
  have eq634 : (k y (τ (σ y))) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq211 y (σ y)
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq211
    | exact resolve eq211 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq641 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq619
       grind)
    | exact superpose eq619 eq12
    | exact resolve eq12 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq642 : (σ x) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq641
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq641
    | exact resolve eq641 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq644 : x = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq634
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq634
    | exact resolve eq634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq645 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq644
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq644
    | exact resolve eq644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq652 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq197 y y
       have i₂ := eq645
       grind)
    | exact superpose eq645 eq197
    | (have j0 := eq197 x y
       grind)
    | exact resolve eq197 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq652
  have eq661 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq653
       grind)
    | exact superpose eq653 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq653
       grind)
    | exact resolve eq12 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : x ≠ y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq653
  have eq663 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq661
  have eq667 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq645
       have i₂ := eq663
       grind)
    | exact superpose eq663 eq645
    | exact resolve eq645 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq663
  have eq678 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq667
  have eq681 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq678
       have r₂ := eq662
       grind)
    | exact resolve eq678 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq678
  have eq886 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq642
       have r₂ := eq681
       grind)
    | exact resolve eq642 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq681
  have eq892 : (k y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq886
       grind)
    | exact superpose eq886 eq10
    | exact resolve eq10 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq930 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq892
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq892
    | exact resolve eq892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq940 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq197 y y
       have i₂ := eq930
       grind)
    | exact superpose eq930 eq197
    | (have j0 := eq197 x y
       grind)
    | exact resolve eq197 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq941 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq940
  have eq956 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq941
       grind)
    | exact superpose eq941 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq941
       grind)
    | exact resolve eq12 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq941
  have eq958 : y = (k y y) ∨ x = (M.op y y) := by grind
  clear eq956
  have eq979 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq66 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq987 : x = y ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq930
       have i₂ := eq958
       grind)
    | exact superpose eq958 eq930
    | exact resolve eq930 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930 eq958
  have eq1002 : x = y ∨ x = (M.op y y) := by grind
  clear eq987
  have eq1006 : x = (M.op y y) := by
    first
    | (have r₁ := eq1002
       have r₂ := eq957
       grind)
    | exact resolve eq1002 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq1002
  have eq1011 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq9
    | exact resolve eq9 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X1) = (M.op (M.op X0 x) y) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 y X1
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq62
    | exact resolve eq62 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1015 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op (M.op X1 x) y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq63
    | exact resolve eq63 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1018 : ∀ X0 : G, (M.op (M.op X0 x) y) ≠ X0 ∨ (k X0 X0) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq65 X0 y
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq65
    | exact resolve eq65 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1074 : (k y (M.op x x)) = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq979 y
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq979
    | exact resolve eq979 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq9838 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (M.op (σ X0) x) y) ∨ (σ X0) = (M.op (M.op (σ X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 X1
       have i₂ := eq1013 (σ X0) X1
       grind)
    | exact superpose eq1013 eq369
    | (have j0 := eq369 X0 X1
       grind)
    | exact resolve eq369 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq9839 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (M.op (σ X0) x) y) ∨ (σ X0) = (M.op (M.op (σ X0) x) y) := by
    intro X0
    first
    | (have i₁ := eq9838 X0 x
       have i₂ := eq1013 (σ X0) x
       grind)
    | exact superpose eq1013 eq9838
    | (have j0 := eq9838 X0 x
       grind)
    | exact resolve eq9838 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013 eq9838
  have eq10630 : ∀ X0 : G, (k X0 (σ (τ X0))) = (M.op (M.op (σ (τ X0)) x) y) ∨ (σ (τ X0)) = (M.op (M.op (σ (τ X0)) x) y) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq9839 (τ X0)
       grind)
    | exact superpose eq9839 eq18
    | (have j1 := eq9839 (τ X0)
       grind)
    | exact resolve eq18 eq9839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9839
  have eq10688 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 x) y) ∨ (σ (τ X0)) = (M.op (M.op (σ (τ X0)) x) y) := by
    intro X0
    first
    | (have i₁ := eq10630 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10630
    | (have j0 := eq10630 X0
       grind)
    | exact resolve eq10630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10630
  have eq10712 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ (k X0 X0) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq10688 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10688
    | (have j0 := eq10688 X0
       grind)
    | exact resolve eq10688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10688
  have eq10727 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have j0 := eq10712 X0
       have j1 := eq1018 X0
       grind)
    | (have r₁ := eq10712 X0
       have r₂ := eq1018 X0
       grind)
    | exact resolve eq10712 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq10712
  have eq10766 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (M.op (σ X0) x) y) := by
    intro X0
    first
    | (have i₁ := eq10727 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq10727
    | exact resolve eq10727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10776 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10727 X0
       have i₂ := eq1011 X0
       grind)
    | exact superpose eq1011 eq10727
    | exact resolve eq10727 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10838 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (M.op (M.op (σ X0) x) y)) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq10727 (σ X0)
       grind)
    | exact superpose eq10727 eq29
    | exact resolve eq29 eq10727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq10899 : ∀ X0 : G, (k X0 X0) = (τ (M.op (M.op (σ X0) x) y)) := by
    intro X0
    first
    | (have i₁ := eq10838 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10838
    | exact resolve eq10838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10838
  have eq11021 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq10776 (σ X0)
       grind)
    | exact superpose eq10776 eq15
    | exact resolve eq15 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11075 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11021 X0
       have i₂ := eq10776 X0
       grind)
    | exact superpose eq10776 eq11021
    | exact resolve eq11021 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11021
  have eq11789 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) x) y) := by
    intro X0
    first
    | (have i₁ := eq10766 X0
       have i₂ := eq10776 X0
       grind)
    | exact superpose eq10776 eq10766
    | exact resolve eq10766 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10766 eq10776
  have eq12074 : ∀ X0 : G, (M.op (M.op X0 x) y) = (τ (M.op (M.op (σ X0) x) y)) := by
    intro X0
    first
    | (have i₁ := eq10899 X0
       have i₂ := eq10727 X0
       grind)
    | exact superpose eq10727 eq10899
    | exact resolve eq10899 eq10727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10727 eq10899
  have eq12691 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1015 X1 (σ X0)
       have i₂ := eq11789 X0
       grind)
    | exact superpose eq11789 eq1015
    | exact resolve eq1015 eq11789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq11789
  have eq17260 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12691 y X0
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq12691
    | exact resolve eq12691 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17675 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq17260 X0
       have i₂ := eq1011 X0
       grind)
    | exact superpose eq1011 eq17260
    | exact resolve eq17260 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq17700 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq17260 (σ x)
       have i₂ := eq11075 x
       grind)
    | exact superpose eq11075 eq17260
    | exact resolve eq17260 eq11075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17260
  have eq17911 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k (σ y) (σ (M.op x x))) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq12 (σ y) (σ (M.op x x))
       have i₂ := eq17700
       grind)
    | exact superpose eq17700 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x x))
       have r₂ := eq17700
       grind)
    | exact resolve eq12 eq17700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17700
  have eq17912 : (k (σ y) (σ (M.op x x))) = (M.op (σ y) (σ (M.op x x))) := by grind
  clear eq17911
  have eq17913 : (σ (k y (M.op x x))) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq17912
       have i₂ := eq15 y (M.op x x)
       grind)
    | exact superpose eq15 eq17912
    | exact resolve eq17912 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17912
  have eq17919 : (σ (M.op y (M.op x x))) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq17913
       have i₂ := eq1074
       grind)
    | exact superpose eq1074 eq17913
    | exact resolve eq17913 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq17913
  have eq20617 : (M.op (σ y) (σ y)) = (M.op (σ (M.op y (M.op x x))) (σ x)) := by
    first
    | (have i₁ := eq12691 x (σ y)
       have i₂ := eq17919
       grind)
    | exact superpose eq17919 eq12691
    | exact resolve eq12691 eq17919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12691 eq17919
  have eq20625 : (σ (M.op y y)) = (M.op (σ (M.op y (M.op x x))) (σ x)) := by
    first
    | (have i₁ := eq20617
       have i₂ := eq11075 y
       grind)
    | exact superpose eq11075 eq20617
    | exact resolve eq20617 eq11075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11075 eq20617
  have eq20631 : (σ x) = (M.op (σ (M.op y (M.op x x))) (σ x)) := by
    first
    | (have i₁ := eq20625
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq20625
    | exact resolve eq20625 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20625
  have eq20638 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op y (M.op x x))) x) y) := by
    first
    | (have i₁ := eq17675 (σ (M.op y (M.op x x)))
       have i₂ := eq20631
       grind)
    | exact superpose eq20631 eq17675
    | exact resolve eq17675 eq20631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17675 eq20631
  have eq40551 : (M.op (M.op (M.op y (M.op x x)) x) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12074 (M.op y (M.op x x))
       have i₂ := eq20638
       grind)
    | exact superpose eq20638 eq12074
    | exact resolve eq12074 eq20638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12074 eq20638
  have eq40576 : (M.op (M.op y y) y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40551
       have i₂ := eq9 y x
       grind)
    | exact superpose eq9 eq40551
    | exact resolve eq40551 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40551
  have eq40586 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40576
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq40576
    | exact resolve eq40576 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq40576
  have eq40603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq40586
       grind)
    | exact superpose eq40586 eq11
    | exact resolve eq11 eq40586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40586
  have eq40647 : False := by grind
  exact eq40647

/-- `Equation3873`: `x ◇ x = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation3873 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3873 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3873.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq126 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq139 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq126
    | (have j0 := eq126 X0 X1
       grind)
    | exact resolve eq126 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq145 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq139 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq139 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq594 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq145
    | exact resolve eq145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq145 (σ X1) X0
       grind)
    | exact superpose eq145 eq15
    | (have j1 := eq145 (σ X1) X0
       grind)
    | exact resolve eq15 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq633 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq594 X0 (τ X1)
       grind)
    | exact superpose eq594 eq17
    | (have j1 := eq594 X0 (τ X1)
       grind)
    | exact resolve eq17 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq594
  have eq1246 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq633
    | exact resolve eq633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq1322 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1246 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1246
    | (have j0 := eq1246 X0 X1
       grind)
    | exact resolve eq1246 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq2615 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq605 x y
       grind)
    | exact superpose eq605 eq16
    | (have j1 := eq605 x y
       grind)
    | exact resolve eq16 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2651 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq605 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq3040 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2615
       have i₂ := eq1322 y x
       grind)
    | exact superpose eq1322 eq2615
    | (have j1 := eq1322 (σ y) (σ x)
       grind)
    | (have r₁ := eq2615
       have r₂ := eq1322 y x
       grind)
    | exact resolve eq2615 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq3041 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3040
  have eq3045 : x ≠ (M.op x x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq12
    | exact resolve eq12 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3046 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3041
       grind)
    | exact superpose eq3041 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3041
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3041
       grind)
    | exact resolve eq13 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041
  have eq3055 : x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3046
  have eq3056 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3045
       have r₂ := eq3055
       grind)
    | exact resolve eq3045 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045 eq3055
  have eq3135 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2651 x y
       have i₂ := eq3056
       grind)
    | exact superpose eq3056 eq2651
    | (have j0 := eq2651 x y
       grind)
    | exact resolve eq2651 eq3056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651 eq3056
  have eq3140 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3135
  have eq3141 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3140
  have eq3156 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3141
       grind)
    | exact superpose eq3141 eq16
    | exact resolve eq16 eq3141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3157 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq3141
       grind)
    | exact superpose eq3141 eq78
    | exact resolve eq78 eq3141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3160 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3141
       grind)
    | exact superpose eq3141 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3141
       grind)
    | exact resolve eq13 eq3141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3141
  have eq3169 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3160
  have eq3174 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3169
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3169
    | exact resolve eq3169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3176 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3157
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3157
    | exact resolve eq3157 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157
  have eq3181 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq3174
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq3174
    | exact resolve eq3174 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3174
  have eq3185 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq3181
       have r₂ := eq3176
       grind)
    | exact resolve eq3181 eq3176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176 eq3181
  have eq3300 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1322 y x
       have i₂ := eq3185
       grind)
    | exact superpose eq3185 eq1322
    | (have j0 := eq1322 y x
       grind)
    | exact resolve eq1322 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq3185
  have eq3356 : x = (M.op x y) := by
    first
    | (have r₁ := eq3300
       have r₂ := eq3156
       grind)
    | exact resolve eq3300 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300
  have eq3596 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3156
       have i₂ := eq3356
       grind)
    | exact superpose eq3356 eq3156
    | exact resolve eq3156 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156 eq3356
  have eq3614 : False := by grind
  exact eq3614

/-- `Equation3873`: `x ◇ x = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation3873 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3873 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3873.models_iff G M).mp hM
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq169 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq185 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq191 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq185 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq185 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq201
    | exact resolve eq201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq296 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq205 X0 (τ X1)
       grind)
    | exact superpose eq205 eq17
    | exact resolve eq17 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq205
  have eq310 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq296
    | exact resolve eq296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq316 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq310
    | exact resolve eq310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq328 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq216
       have i₂ := eq316 x y
       grind)
    | exact superpose eq316 eq216
    | exact resolve eq216 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq316
  have eq329 : False := by grind
  exact eq329

/-- `Equation3873`: `x ◇ x = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation3873 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3873 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3873.models_iff G M).mp hM
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
  have eq927 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
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
  have eq944 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq952 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq961 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq944 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq944
    | (have j0 := eq944 X0 X1
       grind)
    | exact resolve eq944 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq980 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq961 x y
       grind)
    | exact superpose eq961 eq16
    | (have j1 := eq961 x y
       grind)
    | exact resolve eq16 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq961 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq5944 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq952 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq952
    | exact resolve eq952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq6027 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5944 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5944
    | (have j0 := eq5944 X0 X1
       grind)
    | exact resolve eq5944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5944
  have eq11165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq980
       have i₂ := eq6027 y x
       grind)
    | exact superpose eq6027 eq980
    | (have j1 := eq6027 y x
       grind)
    | (have r₁ := eq980
       have r₂ := eq6027 y x
       grind)
    | (have r₁ := eq980
       have r₂ := eq6027 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq980
       have r₂ := eq6027 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq980 eq6027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980 eq6027
  have eq11166 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq11165
  have eq11185 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq988 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq988
    | (have j0 := eq988 (τ X1) (τ X0)
       grind)
    | exact resolve eq988 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq11243 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11185 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq11185
    | (have j0 := eq11185 X0 X1
       grind)
    | exact resolve eq11185 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11185
  have eq11278 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11243 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11243
    | (have j0 := eq11243 X0 X1
       grind)
    | exact resolve eq11243 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11243
  have eq11310 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11278 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11278
    | (have j0 := eq11278 X0 X1
       grind)
    | exact resolve eq11278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11278
  have eq11336 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11310 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11310
    | (have j0 := eq11310 X0 X1
       grind)
    | exact resolve eq11310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11310
  have eq11356 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11336 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq11336
    | (have j0 := eq11336 X0 X1
       grind)
    | exact resolve eq11336 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11336
  have eq11375 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11356 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11356
    | (have j0 := eq11356 X0 X1
       grind)
    | exact resolve eq11356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11356
  have eq11388 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11375 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11375
    | (have j0 := eq11375 X0 X1
       grind)
    | exact resolve eq11375 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11375
  have eq22917 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11166
       grind)
    | exact superpose eq11166 eq16
    | exact resolve eq16 eq11166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11166
  have eq22918 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq22917
       have r₂ := eq22 x
       grind)
    | exact resolve eq22917 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22917
  have eq22920 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22918
       grind)
    | exact superpose eq22918 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22918
       grind)
    | exact resolve eq13 eq22918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22918
  have eq22929 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq22920
  have eq26990 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22929
       grind)
    | exact superpose eq22929 eq16
    | exact resolve eq16 eq22929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22929
  have eq26991 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq26990
       have r₂ := eq22 x
       grind)
    | exact resolve eq26990 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26990
  have eq26994 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq927 x (σ y)
       have i₂ := eq26991
       grind)
    | exact superpose eq26991 eq927
    | (have j0 := eq927 x (σ y)
       grind)
    | (have r₁ := eq927 x (σ y)
       have r₂ := eq26991
       grind)
    | exact resolve eq927 eq26991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26991
  have eq27018 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq26994
  have eq27019 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq27018
  have eq27031 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq27019
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq27019
    | exact resolve eq27019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27019
  have eq27041 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq988 x y
       have i₂ := eq27031
       grind)
    | exact superpose eq27031 eq988
    | (have j0 := eq988 x y
       grind)
    | (have r₁ := eq988 x y
       have r₂ := eq27031
       grind)
    | exact resolve eq988 eq27031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27031
  have eq27068 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq27041
  have eq27069 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq27068
  have eq27074 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq988 x y
       grind)
    | (have r₁ := eq27069
       have r₂ := eq988 x y
       grind)
    | exact resolve eq27069 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq27069
  have eq27077 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27074
       grind)
    | exact superpose eq27074 eq16
    | exact resolve eq16 eq27074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27078 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq927 x (σ y)
       have i₂ := eq27074
       grind)
    | exact superpose eq27074 eq927
    | (have j0 := eq927 x (σ y)
       grind)
    | (have r₁ := eq927 x (σ y)
       have r₂ := eq27074
       grind)
    | exact resolve eq927 eq27074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq27074
  have eq27102 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq27078
  have eq27103 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq27102
  have eq27115 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq27103
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq27103
    | exact resolve eq27103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27103
  have eq27122 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27115
       grind)
    | exact superpose eq27115 eq10
    | exact resolve eq10 eq27115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27115
  have eq27279 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq27122
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq27122
    | exact resolve eq27122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27122
  have eq27281 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27279
       grind)
    | exact superpose eq27279 eq16
    | exact resolve eq16 eq27279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27279
  have eq27282 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq27281
       have r₂ := eq22 x
       grind)
    | exact resolve eq27281 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27281
  have eq27296 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq27282
       grind)
    | exact superpose eq27282 eq10
    | exact resolve eq10 eq27282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27282
  have eq27454 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq27296
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq27296
    | exact resolve eq27296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27296
  have eq27709 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11388 y x
       have i₂ := eq27454
       grind)
    | exact superpose eq27454 eq11388
    | (have j0 := eq11388 y x
       grind)
    | (have r₁ := eq11388 y x
       have r₂ := eq27454
       grind)
    | exact resolve eq11388 eq27454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11388 eq27454
  have eq27713 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq27709
  have eq27717 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27713
       grind)
    | exact superpose eq27713 eq16
    | exact resolve eq16 eq27713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27713
  have eq27720 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq27717
       have r₂ := eq22 x
       grind)
    | exact resolve eq27717 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27717
  have eq27721 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27077
       have i₂ := eq27720
       grind)
    | exact superpose eq27720 eq27077
    | exact resolve eq27077 eq27720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27077
  have eq27743 : (σ x) = (σ y) := by grind
  clear eq27721
  have eq27744 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27743
       grind)
    | exact superpose eq27743 eq16
    | exact resolve eq16 eq27743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27743
  have eq27903 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27744
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq27744
    | exact resolve eq27744 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27744
  have eq27904 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq27903
       have i₂ := eq27720
       grind)
    | exact superpose eq27720 eq27903
    | exact resolve eq27903 eq27720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27720 eq27903
  have eq27905 : False := by grind
  exact eq27905

/-- `Equation3874`: `x ◇ x = (x ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_y_pyx_Equation3874 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X2 X3)) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X0 (M.op (M.op X1 X2) X3))) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X2
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq63 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) (M.op X0 (M.op (M.op x y) X1))) = (M.op (M.op X0 X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 (M.op sF0 x))
       have i₂ := eq9 X0 sF0 x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (M.op X0 (M.op (M.op (σ x) (σ y)) X1))) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 (M.op sF4 x))
       have i₂ := eq9 X0 sF4 x
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq130 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq212 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1124 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq58
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq58
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1136 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1124
    | exact resolve eq1124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1138 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0)) X1 X2 X3
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2638 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 x) x)) X0 (M.op (M.op X1 x) x)
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2648 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) (M.op X0 (M.op (M.op X1 X3) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X3) X4)) (M.op X0 (M.op (M.op X1 X3) X4))
       have i₂ := eq54 X0 X1 X3 X4
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2757 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1085 X0 X1
       grind)
    | exact superpose eq1085 eq10
    | (have j1 := eq1085 X1 X1
       grind)
    | exact resolve eq10 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq2890 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq52 eq2638
    | exact resolve eq2638 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2899 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq2638 X0 (M.op X0 X1)
       grind)
    | exact superpose eq2638 eq9
    | exact resolve eq9 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2904 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq52 (M.op x x)
       have i₂ := eq2638 x sF0
       grind)
    | exact superpose eq2638 eq52
    | exact resolve eq52 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2905 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq55 (M.op sF2 sF2)
       have i₂ := eq2638 sF2 sF4
       grind)
    | exact superpose eq2638 eq55
    | exact resolve eq55 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq2925 : (M.op (M.op (M.op x y) (M.op x y)) x) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2890 eq52
    | exact resolve eq52 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq2929 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq52 eq2925
    | exact resolve eq2925 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925
  have eq2945 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X0 (M.op (M.op x y) (M.op x y))) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2929 eq12
    | (have j0 := eq12 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op x y) (M.op x y))
       have r₂ := eq2929
       grind)
    | exact resolve eq12 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2955 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq2945 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945
  have eq3005 : ∀ X0 : G, (k (τ X0) (τ (M.op (M.op x y) (M.op x y)))) = (τ (M.op X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq2955 eq130
    | exact resolve eq130 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq4633 : ∀ X0 : G, (k (τ (M.op X0 (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq77 eq3005
    | exact resolve eq3005 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4637 : (τ (M.op (M.op x y) (M.op x y))) = (k (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq2929 eq3005
    | exact resolve eq3005 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq4671 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (k (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3005 eq4633
    | exact resolve eq4633 eq3005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005 eq4633
  have eq4793 : (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) ∨ (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) ∨ (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq4637 eq14
    | (have j0 := eq14 (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq14 eq4637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4637
  have eq4795 : (τ (M.op (M.op x y) (M.op x y))) = (M.op (τ (M.op (M.op x y) (M.op x y))) (τ (M.op (M.op x y) (M.op x y)))) := by grind
  clear eq4793
  have eq4814 : ∀ X0 : G, (τ (M.op (M.op x y) (M.op x y))) ≠ (τ (M.op (M.op x y) (M.op x y))) ∨ (k X0 (τ (M.op (M.op x y) (M.op x y)))) = (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4795 eq12
    | (have j0 := eq12 X0 (τ (M.op (M.op x y) (M.op x y)))
       grind)
    | (have r₁ := eq12 X0 (τ (M.op (M.op x y) (M.op x y)))
       have r₂ := eq4795
       grind)
    | exact resolve eq12 eq4795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4823 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4795 eq9
    | exact resolve eq9 eq4795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4795
  have eq4825 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) (M.op x y)))) = (M.op X0 (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq4814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814
  have eq4858 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (M.op (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4825 eq4671
    | exact resolve eq4671 eq4825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq4903 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ X0) (τ (M.op (M.op x y) (M.op x y)))) (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4825 eq4858
    | exact resolve eq4858 eq4825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4825 eq4858
  have eq4923 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq4823 eq4903
    | exact resolve eq4903 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823 eq4903
  have eq4994 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4923 (M.op X0 (M.op X0 X0))
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq4923
    | exact resolve eq4923 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4996 : (M.op (τ (M.op x x)) (τ (M.op x x))) = (τ (M.op (M.op x x) (M.op x y))) := by
    first
    | (have i₁ := eq4923 (M.op x x)
       have i₂ := eq2904
       grind)
    | exact superpose eq2904 eq4923
    | exact resolve eq4923 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5000 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq4923 X0
       grind)
    | exact superpose eq4923 eq11
    | exact resolve eq11 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5002 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ X1)) = (σ (k (M.op (τ X0) (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op X0 X0) X1
       have i₂ := eq4923 X0
       grind)
    | exact superpose eq4923 eq49
    | exact resolve eq49 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5034 : (τ (M.op (M.op x x) (M.op x y))) = (M.op (M.op (τ x) (τ x)) (M.op (τ x) (τ x))) := by
    first
    | (have i₁ := eq4996
       have i₂ := eq4923 x
       grind)
    | exact superpose eq4923 eq4996
    | exact resolve eq4996 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4996
  have eq5035 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4994 X0
       have i₂ := eq4923 X0
       grind)
    | exact superpose eq4923 eq4994
    | exact resolve eq4994 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq5041 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5000 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5000
    | exact resolve eq5000 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5000
  have eq5216 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op x y))) := by
    first
    | (have i₁ := eq5041 (M.op x x)
       have i₂ := eq2904
       grind)
    | exact superpose eq2904 eq5041
    | exact resolve eq5041 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq5224 : ∀ X0 : G, (σ (k (M.op X0 X0) (M.op x y))) = (k (M.op (σ X0) (σ X0)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op X0 X0)
       have i₂ := eq5041 X0
       grind)
    | exact superpose eq5041 eq29
    | exact resolve eq29 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5262 : (σ (M.op (M.op x x) (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5216
       have i₂ := eq5041 x
       grind)
    | exact superpose eq5041 eq5216
    | exact resolve eq5216 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5216
  have eq5265 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x y))) := by
    first
    | (have i₁ := eq5262
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5262
    | exact resolve eq5262 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5262
  have eq5266 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x y))) := by
    first
    | exact superpose eq2905 eq5265
    | exact resolve eq5265 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905 eq5265
  have eq5657 : (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ (M.op x y))) = (σ (k (M.op (M.op x x) (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq5266 eq29
    | exact resolve eq29 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5658 : (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) = (σ (k (M.op (M.op x x) (M.op x y)) x)) := by
    first
    | exact superpose eq5266 eq30
    | exact resolve eq30 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6340 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1138 X0 X1 (M.op X0 (M.op X0 X0)) (M.op x x)
       have i₂ := eq1138 X0 X0 x x
       grind)
    | exact superpose eq1138 eq1138
    | exact resolve eq1138 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6355 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ≠ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))
       have i₂ := eq1138 X0 (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq1138 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6356 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) ≠ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1
       have i₂ := eq1138 X0 (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq1138 eq13
    | (have j0 := eq13 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1
       grind)
    | exact resolve eq13 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6358 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) X1) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1 X2 X3
       have i₂ := eq1138 X0 (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq1138 eq54
    | exact resolve eq54 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6359 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) x) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op x y) X1)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1
       have i₂ := eq1138 X0 (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq1138 eq76
    | exact resolve eq76 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6361 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (σ x)) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op (σ x) (σ y)) X1)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1
       have i₂ := eq1138 X0 (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq1138 eq78
    | exact resolve eq78 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6365 : ∀ X0 : G, (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq4923 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))
       have i₂ := eq1138 X0 (M.op X0 (M.op X0 X0)) X0 X0
       grind)
    | exact superpose eq1138 eq4923
    | exact resolve eq4923 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq6371 : ∀ X0 : G, (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0)))) = (M.op (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6365 X0
       have i₂ := eq4923 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq4923 eq6365
    | exact resolve eq6365 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6365
  have eq6374 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op (σ x) (σ y)) X1)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6361 X0 X1
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6361
    | exact resolve eq6361 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6361
  have eq6376 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op x y) X1)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6359 X0 X1
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6359
    | exact resolve eq6359 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359
  have eq6377 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) (M.op (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6358 X0 X1 X2 X3
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6358
    | exact resolve eq6358 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6358
  have eq6379 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6356 X0 X1
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6356
    | (have j0 := eq6356 X0 X1
       grind)
    | exact resolve eq6356 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6356
  have eq6380 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6355 X0 X1
       have i₂ := eq53 X0 X0 X0 X0
       grind)
    | exact superpose eq53 eq6355
    | (have j0 := eq6355 X0 X1
       grind)
    | exact resolve eq6355 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq6355
  have eq6400 : ∀ X0 : G, (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0)))) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6371 X0
       have i₂ := eq6340 X0 X0
       grind)
    | exact superpose eq6340 eq6371
    | exact resolve eq6371 eq6340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6371
  have eq6403 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) X1)) (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6374 X0 X1
       have i₂ := eq6340 X0 X0
       grind)
    | exact superpose eq6340 eq6374
    | exact resolve eq6374 eq6340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6374
  have eq6405 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op (M.op (M.op X0 X0) (M.op (M.op x y) X1)) (M.op (M.op X0 X0) (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6376 X0 X1
       have i₂ := eq6340 X0 X0
       grind)
    | exact superpose eq6340 eq6376
    | exact resolve eq6376 eq6340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376
  have eq6406 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6377 X0 X1 X2 X3
       have i₂ := eq6340 X0 X0
       grind)
    | exact superpose eq6340 eq6377
    | exact resolve eq6377 eq6340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6377
  have eq6408 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6379 X0 X1
       grind)
    | (have r₁ := eq6379 X0 X1
       have r₂ := eq6340 X0 X0
       grind)
    | exact resolve eq6379 eq6340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379
  have eq6409 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq6380 X0 X1
       grind)
    | (have r₁ := eq6380 X0 X1
       have r₂ := eq6340 X0 X0
       grind)
    | exact resolve eq6380 eq6340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6380
  have eq6414 : ∀ X0 : G, (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0)))) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6400 X0
       have i₂ := eq4923 X0
       grind)
    | exact superpose eq4923 eq6400
    | exact resolve eq6400 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6400
  have eq6416 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6408 X0 X1
       have i₂ := eq6340 X0 X0
       grind)
    | exact superpose eq6340 eq6408
    | (have j0 := eq6408 X0 X1
       grind)
    | exact resolve eq6408 eq6340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6408
  have eq6417 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6409 X0 X1
       have i₂ := eq6340 X0 X0
       grind)
    | exact superpose eq6340 eq6409
    | exact resolve eq6409 eq6340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6340 eq6409
  have eq6421 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6414 X0
       have i₂ := eq5035 X0
       grind)
    | exact superpose eq5035 eq6414
    | exact resolve eq6414 eq5035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035 eq6414
  have eq6562 : (M.op (τ x) (τ x)) = (τ (M.op (M.op x x) (M.op x y))) := by
    first
    | (have i₁ := eq5034
       have i₂ := eq6421 x
       grind)
    | exact superpose eq6421 eq5034
    | exact resolve eq5034 eq6421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034 eq6421
  have eq6751 : ∀ X0 X1 : G, (k (τ X0) (τ (M.op X1 X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 (M.op X1 X1)
       have i₂ := eq6417 X1 X0
       grind)
    | exact superpose eq6417 eq130
    | exact resolve eq130 eq6417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq6762 : ∀ X0 X1 : G, (k (τ X0) (M.op (τ X1) (τ X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6751 X0 X1
       have i₂ := eq4923 X1
       grind)
    | exact superpose eq4923 eq6751
    | exact resolve eq6751 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6751
  have eq6800 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X1) (τ X1))) = (τ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6762 X0 X1
       have i₂ := eq6417 (τ X1) (τ X0)
       grind)
    | exact superpose eq6417 eq6762
    | exact resolve eq6762 eq6417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6762
  have eq6995 : (M.op (M.op x x) (M.op x y)) = (σ (M.op (τ x) (τ x))) := by
    first
    | exact superpose eq6562 eq11
    | exact resolve eq11 eq6562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6562
  have eq7041 : (M.op (σ (τ x)) (σ (τ x))) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq6995
       have i₂ := eq5041 (τ x)
       grind)
    | exact superpose eq5041 eq6995
    | exact resolve eq6995 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6995
  have eq7061 : (M.op x x) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq7041
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq7041
    | exact resolve eq7041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7041
  have eq7077 : (σ (M.op x x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq7061 eq5266
    | exact resolve eq5266 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5266
  have eq7079 : (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ (M.op x y))) = (σ (k (M.op x x) (M.op x y))) := by
    first
    | exact superpose eq7061 eq5657
    | exact resolve eq5657 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5657
  have eq7080 : (k (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) = (σ (k (M.op x x) x)) := by
    first
    | exact superpose eq7061 eq5658
    | exact resolve eq5658 eq7061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5658 eq7061
  have eq7113 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7077
       have i₂ := eq5041 x
       grind)
    | exact superpose eq5041 eq7077
    | exact resolve eq7077 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7077
  have eq7122 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq7113
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7113
    | exact resolve eq7113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq7141 : (k (M.op (σ x) (σ x)) (σ (M.op x y))) = (σ (k (M.op x x) (M.op x y))) := by
    first
    | exact superpose eq7122 eq7079
    | exact resolve eq7079 eq7122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7079
  have eq7142 : (k (M.op (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) := by
    first
    | exact superpose eq7122 eq7080
    | exact resolve eq7080 eq7122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7080 eq7122
  have eq7283 : (σ (M.op x y)) = (σ (k (M.op x x) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7141 eq6416
    | (have j0 := eq6416 x (σ (M.op x y))
       grind)
    | exact resolve eq6416 eq7141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7141
  have eq7297 : (σ x) = (σ (k (M.op x x) x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7142 eq6416
    | (have j0 := eq6416 x (σ x)
       grind)
    | exact resolve eq6416 eq7142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7142
  have eq7520 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 X0 X0 X0 X0
       have i₂ := eq2648 X0 X0 X0 X0 X0
       grind)
    | exact superpose eq2648 eq54
    | exact resolve eq54 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7713 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq7520 (M.op x (M.op (M.op x x) x))
       have i₂ := eq2648 x x x x x
       grind)
    | exact superpose eq2648 eq7520
    | exact resolve eq7520 eq2648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq7751 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7713 X0
       have i₂ := eq2899 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq2899 eq7713
    | exact resolve eq7713 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7713
  have eq7765 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2899 X0 X1
       have i₂ := eq7751 X0
       grind)
    | exact superpose eq7751 eq2899
    | exact resolve eq2899 eq7751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899 eq7751
  have eq7813 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7765 (M.op X0 (M.op (M.op X1 x) x)) (M.op X0 (M.op (M.op X1 x) x))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq7765
    | exact resolve eq7765 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7908 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6403 X0 X1
       have i₂ := eq7813 X0 (M.op sF4 X1)
       grind)
    | exact superpose eq7813 eq6403
    | exact resolve eq6403 eq7813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403
  have eq7909 : ∀ X0 X1 : G, (M.op (M.op X0 X0) x) = (M.op (M.op X0 X0) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6405 X0 X1
       have i₂ := eq7813 X0 (M.op sF0 X1)
       grind)
    | exact superpose eq7813 eq6405
    | exact resolve eq6405 eq7813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6405
  have eq7912 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6406 X0 X1 X2 X3
       have i₂ := eq7813 X0 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq7813 eq6406
    | exact resolve eq6406 eq7813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6406 eq7813
  have eq8084 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (σ x) (σ y)) X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq7908 (M.op X0 (M.op (M.op X1 x) x)) X1
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq7908
    | exact resolve eq7908 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8121 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq7908 eq9
    | exact resolve eq9 eq7908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8127 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq7908 eq77
    | exact resolve eq77 eq7908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7908
  have eq8165 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8127 X0
       have i₂ := eq7765 X0 X0
       grind)
    | exact superpose eq7765 eq8127
    | exact resolve eq8127 eq7765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8127
  have eq8171 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq8121 X0
       have i₂ := eq7765 X0 X0
       grind)
    | exact superpose eq7765 eq8121
    | exact resolve eq8121 eq7765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8121
  have eq8193 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq8084 eq8165
    | exact resolve eq8165 eq8084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084 eq8165
  have eq8206 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op (M.op X0 X0) (σ x)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq78 eq8171
    | exact resolve eq8171 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq8171
  have eq8236 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq8193 eq8206
    | exact resolve eq8206 eq8193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8193 eq8206
  have eq8308 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 X0) X1) x) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op x y) X4)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq7909 (M.op X0 (M.op (M.op X1 x) x)) X1
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq7909
    | exact resolve eq7909 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8346 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7909 eq9
    | exact resolve eq9 eq7909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8352 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) x) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq7909 eq77
    | exact resolve eq77 eq7909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7909
  have eq8391 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) x) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8352 X0
       have i₂ := eq7765 X0 X0
       grind)
    | exact superpose eq7765 eq8352
    | exact resolve eq8352 eq7765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8352
  have eq8397 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq8346 X0
       have i₂ := eq7765 X0 X0
       grind)
    | exact superpose eq7765 eq8346
    | exact resolve eq8346 eq7765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8346
  have eq8420 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) x) x) := by
    intro X0
    first
    | exact superpose eq8308 eq8391
    | exact resolve eq8391 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8308 eq8391
  have eq8432 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op (M.op (M.op X0 X0) x) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq76 eq8397
    | exact resolve eq8397 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8397
  have eq8465 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq8432 X0
       have i₂ := eq8420 X0
       grind)
    | exact superpose eq8420 eq8432
    | exact resolve eq8432 eq8420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8420 eq8432
  have eq9199 : (τ (σ (M.op x y))) = (k (M.op x x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7283 eq10
    | exact resolve eq10 eq7283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7283
  have eq9222 : (M.op x y) = (k (M.op x x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq37 eq9199
    | exact resolve eq9199 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9199
  have eq10071 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq20 eq5224
    | (have j0 := eq5224 (M.op x y)
       grind)
    | exact resolve eq5224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10075 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op X0 X0) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5224 eq6416
    | (have j0 := eq6416 X0 (σ (M.op x y))
       grind)
    | exact resolve eq6416 eq5224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5224 eq6416
  have eq10166 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (M.op X0 X0) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq10075 eq10
    | exact resolve eq10 eq10075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10216 : ∀ X0 : G, (M.op x y) = (k (M.op X0 X0) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq37 eq10166
    | exact resolve eq10166 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10166
  have eq10226 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 X0) x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq76 eq10216
    | exact resolve eq10216 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq10216
  have eq12426 : ∀ X0 X1 X4 X5 X6 : G, (M.op (M.op (M.op X0 X0) X1) X4) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X4 X5) X6)) := by
    intro X0 X1 X4 X5 X6
    first
    | (have i₁ := eq7912 (M.op X0 (M.op (M.op X1 x) x)) X1 x x
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq7912
    | exact resolve eq7912 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq12576 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 (M.op X1 X2) (M.op X0 X0)
       have i₂ := eq7912 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq7912 eq77
    | exact resolve eq77 eq7912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7912
  have eq12646 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12576 X0 X1 X2
       have i₂ := eq7765 X0 X0
       grind)
    | exact superpose eq7765 eq12576
    | exact resolve eq12576 eq7765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7765 eq12576
  have eq12756 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12646 X0 x x
       have i₂ := eq12426 X0 x x x sF0
       grind)
    | exact superpose eq12426 eq12646
    | exact resolve eq12646 eq12426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12646
  have eq12910 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X1 X2)) X1 X2
       have i₂ := eq12756 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12756 eq9
    | exact resolve eq9 eq12756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12940 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12910 X0 X1 X2
       have i₂ := eq12426 X0 (M.op X1 X2) X0 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12426 eq12910
    | exact resolve eq12910 eq12426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12426 eq12910
  have eq12982 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12940 X0 X1 X2
       have i₂ := eq2638 X0 (M.op X1 X2)
       grind)
    | exact superpose eq2638 eq12940
    | exact resolve eq12940 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12940
  have eq17810 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (τ (M.op X0 X0)) (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6800 (M.op X0 X0) X1
       have i₂ := eq12982 X0 X1 X1
       grind)
    | exact superpose eq12982 eq6800
    | exact resolve eq6800 eq12982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17862 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17810 X0 X1
       have i₂ := eq4923 X0
       grind)
    | exact superpose eq4923 eq17810
    | exact resolve eq17810 eq4923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17810
  have eq17888 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) X1)) = (M.op (M.op (τ X0) (τ X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17862 X0 X1
       have i₂ := eq12982 (τ X0) (τ X1) (τ X1)
       grind)
    | exact superpose eq12982 eq17862
    | exact resolve eq17862 eq12982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17862
  have eq20040 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) X1)
       have i₂ := eq17888 X0 X1
       grind)
    | exact superpose eq17888 eq11
    | exact resolve eq11 eq17888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20309 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (τ X1))) = (M.op (M.op (σ X0) (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20040 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20040
    | exact resolve eq20040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20040
  have eq24092 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4923 (σ X0)
       have i₂ := eq2757 X0 X0
       grind)
    | exact superpose eq2757 eq4923
    | (have j1 := eq2757 X0 X0
       grind)
    | exact resolve eq4923 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757
  have eq24129 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq24092 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24092
  have eq24145 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24129 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24129
    | (have j0 := eq24129 X0
       grind)
    | exact resolve eq24129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24129
  have eq26020 : ∀ X0 X1 : G, (M.op (M.op (σ X1) (σ X1)) (σ X0)) = (σ (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20309 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20309
    | exact resolve eq20309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26022 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ (M.op x y))) = (σ (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq37 eq20309
    | exact resolve eq20309 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq20309
  have eq26116 : ∀ X0 : G, (σ (M.op (M.op X0 X0) x)) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq8465 eq26022
    | exact resolve eq26022 eq8465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26022
  have eq26213 : ∀ X0 : G, (σ (M.op (M.op X0 X0) x)) = (M.op (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq26116 X0
       have i₂ := eq212 (σ X0) sF1
       grind)
    | exact superpose eq212 eq26116
    | exact resolve eq26116 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26116
  have eq26280 : ∀ X0 : G, (M.op (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (M.op (M.op (σ X0) (σ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq26213 X0
       have i₂ := eq26020 x X0
       grind)
    | exact superpose eq26020 eq26213
    | exact resolve eq26213 eq26020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26213
  have eq26322 : ∀ X0 : G, (M.op (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (M.op (M.op (σ X0) (σ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq26280 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26280
    | (have j0 := eq26280 X0
       grind)
    | exact resolve eq26280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26280
  have eq26345 : ∀ X0 : G, (M.op (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (M.op (M.op (σ X0) (M.op (σ x) (σ x))) (M.op (σ X0) (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq26322 X0
       have i₂ := eq212 (σ X0) sF2
       grind)
    | exact superpose eq212 eq26322
    | exact resolve eq26322 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26322
  have eq26429 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq49 X0 (τ X0)
       have i₂ := eq24145 (τ X0)
       grind)
    | exact superpose eq24145 eq49
    | (have j1 := eq24145 (τ X0)
       grind)
    | exact resolve eq49 eq24145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq24145
  have eq26496 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26429 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26429
    | (have j0 := eq26429 X0
       grind)
    | exact resolve eq26429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26429
  have eq26546 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26496 X0
       have i₂ := eq5041 (τ X0)
       grind)
    | exact superpose eq5041 eq26496
    | (have j0 := eq26496 X0
       grind)
    | exact resolve eq26496 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26496
  have eq26569 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26546 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26546
    | (have j0 := eq26546 X0
       grind)
    | exact resolve eq26546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26546
  have eq26580 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq26569 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26569
    | (have j0 := eq26569 X0
       grind)
    | exact resolve eq26569 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26569
  have eq26584 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26580 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq26580 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq26580 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26580
  have eq46498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1136
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1136
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq1136 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq46542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq46498
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq46498
    | exact resolve eq46498 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46498
  have eq46545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq46542
    | exact resolve eq46542 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46542
  have eq46546 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq46545
       have r₂ := eq27
       grind)
    | exact resolve eq46545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46545
  have eq46566 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq46546 eq4923
    | exact resolve eq4923 eq46546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46546
  have eq46721 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39 eq46566
    | exact resolve eq46566 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46566
  have eq46722 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq46721
  have eq46750 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq46722 eq4923
    | exact resolve eq4923 eq46722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46722
  have eq46893 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq46750
    | exact resolve eq46750 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46750
  have eq46894 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq46893
  have eq46928 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5041 y
       have i₂ := eq46894
       grind)
    | exact superpose eq46894 eq5041
    | exact resolve eq5041 eq46894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46932 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6417 y x
       have i₂ := eq46894
       grind)
    | exact superpose eq46894 eq6417
    | exact resolve eq6417 eq46894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46894
  have eq47055 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq46928
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46928
    | exact resolve eq46928 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq46928
  have eq47681 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq47055 eq6417
    | exact resolve eq6417 eq47055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47055
  have eq48408 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq47681 eq63
    | exact resolve eq63 eq47681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq47681
  have eq48499 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq48408
    | exact resolve eq48408 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48408
  have eq48524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48499
       have i₂ := eq46932 x
       grind)
    | exact superpose eq46932 eq48499
    | exact resolve eq48499 eq46932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46932 eq48499
  have eq48561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq48524
  have eq48567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48561
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq48561
    | exact resolve eq48561 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48561
  have eq48573 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq48567
    | exact resolve eq48567 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48567
  have eq48576 : x = (M.op x x) := by
    first
    | (have r₁ := eq48573
       have r₂ := eq27
       grind)
    | exact resolve eq48573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48573
  have eq48587 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7297
       have i₂ := eq48576
       grind)
    | exact superpose eq48576 eq7297
    | exact resolve eq7297 eq48576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7297
  have eq48623 : (M.op x y) = (k x (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq9222
       have i₂ := eq48576
       grind)
    | exact superpose eq48576 eq9222
    | exact resolve eq9222 eq48576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9222
  have eq48949 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq48587
       have i₂ := eq26584 x
       grind)
    | exact superpose eq26584 eq48587
    | exact resolve eq48587 eq26584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26584 eq48587
  have eq48973 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq48949
       have i₂ := eq5041 x
       grind)
    | exact superpose eq5041 eq48949
    | exact resolve eq48949 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48949
  have eq48994 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq48973
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48973
    | exact resolve eq48973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48973
  have eq48995 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq48994
  have eq49035 : ∀ X0 : G, (M.op (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y))))) = (M.op (M.op (σ X0) (σ x)) (M.op (σ X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq48995 eq26345
    | exact resolve eq26345 eq48995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26345
  have eq49110 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq48995 eq2638
    | exact resolve eq2638 eq48995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49119 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq48995 eq6417
    | exact resolve eq6417 eq48995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49122 : ∀ X0 : G, (M.op (τ X0) (M.op (τ (σ x)) (τ (σ x)))) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq48995 eq6800
    | exact resolve eq6800 eq48995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6800
  have eq49151 : ∀ X0 : G, (M.op (M.op (τ (σ x)) (τ (σ x))) (τ X0)) = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq48995 eq17888
    | exact resolve eq17888 eq48995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17888
  have eq49190 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq48995 eq9
    | exact resolve eq9 eq48995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49214 : ∀ X0 : G, (M.op (M.op x x) (τ X0)) = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq38 eq49151
    | exact resolve eq49151 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49151
  have eq49222 : ∀ X0 : G, (M.op (τ X0) (M.op x x)) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq38 eq49122
    | exact resolve eq49122 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq49122
  have eq49558 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq49119 eq30
    | exact resolve eq30 eq49119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq49760 : ∀ X0 : G, (M.op x (τ X0)) = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq49214 X0
       have i₂ := eq48576
       grind)
    | exact superpose eq48576 eq49214
    | exact resolve eq49214 eq48576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49214
  have eq49767 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq49222 X0
       have i₂ := eq48576
       grind)
    | exact superpose eq48576 eq49222
    | exact resolve eq49222 eq48576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49222
  have eq51775 : ∀ X0 : G, (k (M.op X0 X0) (σ x)) = (M.op (σ (M.op (τ X0) (τ X0))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq5002 X0 x
       have i₂ := eq49558 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq49558 eq5002
    | exact resolve eq5002 eq49558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5002
  have eq51788 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 x)
       have i₂ := eq49558 X0
       grind)
    | exact superpose eq49558 eq10
    | exact resolve eq10 eq49558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51929 : ∀ X0 : G, (k X0 x) = (M.op (τ (σ X0)) x) := by
    intro X0
    first
    | exact superpose eq49767 eq51788
    | exact resolve eq51788 eq49767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49767 eq51788
  have eq51937 : ∀ X0 : G, (k (M.op X0 X0) (σ x)) = (M.op (M.op (σ (τ X0)) (σ (τ X0))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq51775 X0
       have i₂ := eq5041 (τ X0)
       grind)
    | exact superpose eq5041 eq51775
    | exact resolve eq51775 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51775
  have eq51972 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq51929 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq51929
    | exact resolve eq51929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51929
  have eq51980 : ∀ X0 : G, (k (M.op X0 X0) (σ x)) = (M.op (M.op (σ (τ X0)) (M.op (σ x) (σ x))) (M.op (σ (τ X0)) (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq51937 X0
       have i₂ := eq212 (σ (τ X0)) sF2
       grind)
    | exact superpose eq212 eq51937
    | exact resolve eq51937 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51937
  have eq51999 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq49558 X0
       have i₂ := eq51972 X0
       grind)
    | exact superpose eq51972 eq49558
    | exact resolve eq49558 eq51972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49558 eq51972
  have eq52226 : ∀ X0 : G, (k (M.op X0 X0) (σ x)) = (M.op (M.op (σ (τ X0)) (σ x)) (M.op (σ (τ X0)) (σ x))) := by
    intro X0
    first
    | exact superpose eq48995 eq51980
    | exact resolve eq51980 eq48995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51980
  have eq52275 : ∀ X0 : G, (k (M.op X0 X0) (σ x)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq52226 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52226
    | exact resolve eq52226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52226
  have eq52283 : ∀ X0 : G, (k (M.op X0 X0) (σ x)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq52275 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52275
    | (have j0 := eq52275 X0
       grind)
    | exact resolve eq52275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52275
  have eq52289 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq49119 eq52283
    | exact resolve eq52283 eq49119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49119 eq52283
  have eq52298 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 (M.op x y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq51999
    | exact resolve eq51999 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq51999
  have eq52385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 (M.op x y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq52298 X0
       have i₂ := eq5041 X0
       grind)
    | exact superpose eq5041 eq52298
    | exact resolve eq52298 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52298
  have eq52435 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq8465 x
       have i₂ := eq48576
       grind)
    | exact superpose eq48576 eq8465
    | exact resolve eq8465 eq48576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52454 : ∀ X0 : G, x = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12756 x x
       have i₂ := eq48576
       grind)
    | exact superpose eq48576 eq12756
    | exact resolve eq12756 eq48576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12756
  have eq52518 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq52435
       have i₂ := eq48576
       grind)
    | exact superpose eq48576 eq52435
    | exact resolve eq52435 eq48576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48576 eq52435
  have eq53161 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq52454 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52454
    | (have j0 := eq52454 y
       grind)
    | exact resolve eq52454 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52454
  have eq53319 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53161 eq9
    | exact resolve eq9 eq53161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53161
  have eq53674 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq49110
    | (have j0 := eq49110 (σ y)
       grind)
    | exact resolve eq49110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49110
  have eq53743 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq52385 sF0
       have i₂ := eq5041 sF0
       grind)
    | exact superpose eq5041 eq52385
    | exact resolve eq52385 eq5041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5041 eq52385
  have eq53759 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) (M.op (σ (M.op x y)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq53743
       have i₂ := eq212 (σ sF0) sF2
       grind)
    | exact superpose eq212 eq53743
    | exact resolve eq53743 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53743
  have eq53777 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq48995 eq53759
    | exact resolve eq53759 eq48995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48995 eq53759
  have eq53787 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq20 eq53777
    | exact resolve eq53777 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53777
  have eq53796 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq52289 eq53787
    | exact resolve eq53787 eq52289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52289 eq53787
  have eq54246 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq53674 eq49190
    | exact resolve eq49190 eq53674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49190
  have eq54323 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq53674 eq54246
    | exact resolve eq54246 eq53674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54246
  have eq54373 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq54323 eq2638
    | exact resolve eq2638 eq54323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq54377 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq54323 eq4923
    | exact resolve eq4923 eq54323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4923
  have eq54382 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq54323 eq6417
    | exact resolve eq6417 eq54323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54400 : (M.op x y) = (k (M.op (M.op (σ x) (σ y)) x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54323 eq10226
    | exact resolve eq10226 eq54323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54590 : ∀ X0 : G, (M.op (σ X0) (M.op (σ x) (σ y))) = (σ (k X0 (τ (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq54382 eq48
    | exact resolve eq48 eq54382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq54382
  have eq54862 : ∀ X0 : G, (M.op X0 (τ (M.op (σ x) (σ y)))) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq54377 eq6417
    | exact resolve eq6417 eq54377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6417
  have eq54872 : (M.op (τ (M.op (σ x) (σ y))) x) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq54377 eq8465
    | exact resolve eq8465 eq54377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8465
  have eq54915 : ∀ X0 : G, (σ (M.op (τ (M.op (σ x) (σ y))) X0)) = (M.op (M.op (σ (τ (M.op (σ x) (σ y)))) (σ (τ (M.op (σ x) (σ y))))) (σ X0)) := by
    intro X0
    first
    | exact superpose eq54377 eq26020
    | exact resolve eq26020 eq54377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54377
  have eq54958 : ∀ X0 : G, (σ (M.op (τ (M.op (σ x) (σ y))) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54915 X0
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq54915
    | exact resolve eq54915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54915
  have eq54972 : ∀ X0 : G, (M.op (σ X0) (M.op (σ x) (σ y))) = (σ (M.op X0 (τ (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq54862 eq54590
    | exact resolve eq54590 eq54862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54590
  have eq55001 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (σ (M.op (τ (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | exact superpose eq54323 eq54958
    | exact resolve eq54958 eq54323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54958
  have eq55307 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (σ y))) := by
    first
    | exact superpose eq26 eq49760
    | (have j0 := eq49760 (σ y)
       grind)
    | exact resolve eq49760 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq49760
  have eq55380 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq39 eq55307
    | exact resolve eq55307 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq55307
  have eq55408 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq55380
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55380
    | exact resolve eq55380 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq55380
  have eq55442 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq55408 eq54862
    | exact resolve eq54862 eq55408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54862
  have eq55449 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq55408 eq54872
    | exact resolve eq54872 eq55408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54872
  have eq55489 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq55408 eq54972
    | exact resolve eq54972 eq55408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54972
  have eq55493 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (M.op (σ x) (σ y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq55408 eq55001
    | exact resolve eq55001 eq55408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55001 eq55408
  have eq55638 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op (M.op x y) x) (M.op x y))) := by
    first
    | exact superpose eq55449 eq10071
    | exact resolve eq10071 eq55449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10071 eq55449
  have eq56445 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq55442 eq29
    | exact resolve eq29 eq55442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq56535 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op (M.op X0 X0) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq55442 eq10075
    | exact resolve eq10075 eq55442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10075
  have eq56706 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 X0) x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq55442 eq10226
    | exact resolve eq10226 eq55442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10226
  have eq56860 : (M.op x y) = (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq55442 eq54400
    | exact resolve eq54400 eq55442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54400
  have eq57625 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq55442 eq48623
    | exact resolve eq48623 eq55442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48623
  have eq58062 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) x) (M.op x y))) := by
    first
    | exact superpose eq55442 eq55638
    | exact resolve eq55638 eq55442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55442 eq55638
  have eq58133 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq52518 eq57625
    | exact resolve eq57625 eq52518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52518 eq57625
  have eq58688 : (M.op x y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq53319 eq56860
    | exact resolve eq56860 eq53319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56860
  have eq58827 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53319 eq56706
    | exact resolve eq56706 eq53319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53319 eq56706
  have eq58998 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq56535 x
       have i₂ := eq26020 sF0 x
       grind)
    | exact superpose eq26020 eq56535
    | exact resolve eq56535 eq26020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26020 eq56535
  have eq59036 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (M.op (σ X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq55489 eq56445
    | exact resolve eq56445 eq55489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56445
  have eq59388 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (σ (M.op (M.op x y) x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55489 eq58062
    | exact resolve eq58062 eq55489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55489 eq58062
  have eq59778 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54323 eq58688
    | exact resolve eq58688 eq54323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54323 eq58688
  have eq59896 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq58827 X0
       have i₂ := eq12982 X0 X0 X0
       grind)
    | exact superpose eq12982 eq58827
    | exact resolve eq58827 eq12982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12982 eq58827
  have eq60009 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq58998
    | (have j0 := eq58998 X0
       grind)
    | exact resolve eq58998 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq58998
  have eq60086 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55493 eq59388
    | exact resolve eq59388 eq55493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55493 eq59388
  have eq60399 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq59896 X0
       have i₂ := eq7520 X0
       grind)
    | exact superpose eq7520 eq59896
    | exact resolve eq59896 eq7520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7520 eq59896
  have eq60490 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq60009 X0
       have i₂ := eq212 (σ X0) sF1
       grind)
    | exact superpose eq212 eq60009
    | exact resolve eq60009 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq60009
  have eq60546 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq54373 eq60086
    | exact resolve eq60086 eq54373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54373 eq60086
  have eq60848 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ X0) (σ x)) (M.op (σ X0) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq49035 eq60490
    | exact resolve eq60490 eq49035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49035 eq60490
  have eq60888 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq60546
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60546
    | exact resolve eq60546 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq60546
  have eq61056 : (M.op (σ x) (σ y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq53674 eq60888
    | exact resolve eq60888 eq53674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53674 eq60888
  have eq61561 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq59036 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59036
    | exact resolve eq59036 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59036
  have eq62072 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq61561 eq61056
    | exact resolve eq61056 eq61561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61056 eq61561
  have eq62173 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq8236 eq62072
    | exact resolve eq62072 eq8236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8236 eq62072
  have eq62261 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq53796 eq62173
    | exact resolve eq62173 eq53796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53796 eq62173
  have eq62708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62261 eq58133
    | exact resolve eq58133 eq62261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58133
  have eq62900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62261 eq59778
    | exact resolve eq59778 eq62261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59778
  have eq62946 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq62261 eq60399
    | (have j0 := eq60399 X0
       grind)
    | exact resolve eq60399 eq62261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60399
  have eq63002 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ X0) (σ x)) (M.op (σ X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq62261 eq60848
    | (have j0 := eq60848 X0
       grind)
    | exact resolve eq60848 eq62261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60848 eq62261
  have eq63197 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ X0) (σ x)) (M.op (σ X0) (σ x))) := by
    intro X0
    first
    | (have j0 := eq63002 X0
       grind)
    | (have r₁ := eq63002 X0
       have r₂ := eq27
       grind)
    | exact resolve eq63002 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63002
  have eq63251 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq62946 X0
       grind)
    | (have r₁ := eq62946 X0
       have r₂ := eq27
       grind)
    | exact resolve eq62946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62946
  have eq63296 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62900
       have r₂ := eq27
       grind)
    | exact resolve eq62900 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62900
  have eq63409 : x = (M.op x y) := by
    first
    | (have r₁ := eq62708
       have r₂ := eq27
       grind)
    | exact resolve eq62708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62708
  have eq67213 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq63197 x
       have i₂ := eq63251 (M.op (σ x) sF2)
       grind)
    | exact superpose eq63251 eq63197
    | exact resolve eq63197 eq63251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63197 eq63251
  have eq68330 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq63296 eq27
    | exact resolve eq27 eq63296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63296
  have eq71101 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq63409 eq67213
    | exact resolve eq67213 eq63409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67213
  have eq73063 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq63409 eq68330
    | exact resolve eq68330 eq63409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63409 eq68330
  have eq77860 : False := by grind
  exact eq77860

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_pyy_pyx_pyy_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
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
  have eq317 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq317
  have eq323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq323 (σ X0)
       grind)
    | exact superpose eq323 eq15
    | exact resolve eq15 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq323 (τ X0)
       grind)
    | exact superpose eq323 eq32
    | exact resolve eq32 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq342
    | exact resolve eq342 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq355 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq336 X0
       have i₂ := eq323 X0
       grind)
    | exact superpose eq323 eq336
    | exact resolve eq336 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq336
  have eq403 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq406 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq404 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq404
    | exact resolve eq404 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq412 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq406
  have eq626 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq634 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq643 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1
       have i₂ := eq349 X1
       grind)
    | exact superpose eq349 eq634
    | (have j0 := eq634 X0 X1
       grind)
    | exact resolve eq634 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq651 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 X1
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq626
    | (have j0 := eq626 X0 X1
       grind)
    | exact resolve eq626 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq665 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X1
       have i₂ := eq355 X1
       grind)
    | exact superpose eq355 eq651
    | (have j0 := eq651 X0 X1
       grind)
    | exact resolve eq651 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq4994 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq665 x y
       grind)
    | exact superpose eq665 eq16
    | (have j1 := eq665 x y
       grind)
    | exact resolve eq16 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5013 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq665 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq5632 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq643
    | (have j0 := eq643 X1 (σ X0)
       grind)
    | exact resolve eq643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq5718 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5632 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5632
    | (have j0 := eq5632 X0 X1
       grind)
    | exact resolve eq5632 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5632
  have eq5739 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5718 X0 X1
       have i₂ := eq355 X0
       grind)
    | exact superpose eq355 eq5718
    | (have j0 := eq5718 X0 X1
       grind)
    | exact resolve eq5718 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5718
  have eq5751 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5739 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5739
    | (have j0 := eq5739 X0 X1
       grind)
    | exact resolve eq5739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5739
  have eq11298 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4994
       have i₂ := eq5751 y x
       grind)
    | exact superpose eq5751 eq4994
    | (have j1 := eq5751 y x
       grind)
    | (have r₁ := eq4994
       have r₂ := eq5751 y x
       grind)
    | exact resolve eq4994 eq5751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994 eq5751
  have eq11299 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq11298
  have eq21353 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5013 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq5013
    | (have j0 := eq5013 (τ X1) (τ X0)
       grind)
    | exact resolve eq5013 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq21441 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21353 X0 X1
       have i₂ := eq349 X1
       grind)
    | exact superpose eq349 eq21353
    | (have j0 := eq21353 X0 X1
       grind)
    | exact resolve eq21353 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21353
  have eq21499 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21441 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq21441
    | (have j0 := eq21441 X0 X1
       grind)
    | exact resolve eq21441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21441
  have eq21538 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21499 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq21499
    | (have j0 := eq21499 X0 X1
       grind)
    | exact resolve eq21499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21499
  have eq21570 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21538 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21538
    | (have j0 := eq21538 X0 X1
       grind)
    | exact resolve eq21538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21538
  have eq21594 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21570 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq21570
    | (have j0 := eq21570 X0 X1
       grind)
    | exact resolve eq21570 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21570
  have eq21617 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21594 X0 X1
       have i₂ := eq349 X1
       grind)
    | exact superpose eq349 eq21594
    | (have j0 := eq21594 X0 X1
       grind)
    | exact resolve eq21594 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21594
  have eq21635 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq21617 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq21617
    | (have j0 := eq21617 X0 X1
       grind)
    | exact resolve eq21617 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21617
  have eq21652 : ∀ X0 X1 : G, (σ (τ X1)) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21635 X0 X1
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq21635
    | (have j0 := eq21635 X0 X1
       grind)
    | exact resolve eq21635 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq21635
  have eq21663 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21652 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq21652
    | (have j0 := eq21652 X0 X1
       grind)
    | exact resolve eq21652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21652
  have eq21674 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21663 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq21663
    | (have j0 := eq21663 X0 X1
       grind)
    | exact resolve eq21663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21663
  have eq83793 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq11299
       grind)
    | exact superpose eq11299 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11299
       grind)
    | exact resolve eq13 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11299
  have eq83801 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq83793
  have eq83802 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq83801
  have eq94014 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq403 x (σ y)
       have i₂ := eq83802
       grind)
    | exact superpose eq83802 eq403
    | (have j0 := eq403 x (σ y)
       grind)
    | (have r₁ := eq403 x (σ y)
       have r₂ := eq83802
       grind)
    | exact resolve eq403 eq83802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83802
  have eq94047 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq94014
  have eq94059 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq94047
       have i₂ := eq355 y
       grind)
    | exact superpose eq355 eq94047
    | exact resolve eq94047 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94047
  have eq94060 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq94059
  have eq94068 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq94060
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq94060
    | exact resolve eq94060 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94060
  have eq94101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq412 y
       have i₂ := eq94068
       grind)
    | exact superpose eq94068 eq412
    | exact resolve eq412 eq94068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94068
  have eq94147 : (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq94101
       have r₂ := eq16
       grind)
    | exact resolve eq94101 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94101
  have eq94154 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5013 x y
       have i₂ := eq94147
       grind)
    | exact superpose eq94147 eq5013
    | (have j0 := eq5013 x y
       grind)
    | (have r₁ := eq5013 x y
       have r₂ := eq94147
       grind)
    | exact resolve eq5013 eq94147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94147
  have eq94201 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq94154
  have eq94202 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq94201
  have eq94207 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have j1 := eq5013 x y
       grind)
    | (have r₁ := eq94202
       have r₂ := eq5013 x y
       grind)
    | exact resolve eq94202 eq5013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5013 eq94202
  have eq94212 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94207
       grind)
    | exact superpose eq94207 eq16
    | exact resolve eq16 eq94207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94214 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq403 x (σ y)
       have i₂ := eq94207
       grind)
    | exact superpose eq94207 eq403
    | (have j0 := eq403 x (σ y)
       grind)
    | (have r₁ := eq403 x (σ y)
       have r₂ := eq94207
       grind)
    | exact resolve eq403 eq94207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq94207
  have eq94247 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq94214
  have eq94259 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94247
       have i₂ := eq355 y
       grind)
    | exact superpose eq355 eq94247
    | exact resolve eq94247 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq94247
  have eq94260 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq94259
  have eq94268 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94260
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq94260
    | exact resolve eq94260 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94260
  have eq94305 : (k y x) = (τ (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq94268
       grind)
    | exact superpose eq94268 eq10
    | exact resolve eq10 eq94268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94268
  have eq94525 : (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94305
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq94305
    | exact resolve eq94305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94305
  have eq94685 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq21674 y x
       have i₂ := eq94525
       grind)
    | exact superpose eq94525 eq21674
    | (have j0 := eq21674 y x
       grind)
    | (have r₁ := eq21674 y x
       have r₂ := eq94525
       grind)
    | exact resolve eq21674 eq94525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21674 eq94525
  have eq94698 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq94685
  have eq94705 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94212
       have i₂ := eq94698
       grind)
    | exact superpose eq94698 eq94212
    | exact resolve eq94212 eq94698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94212 eq94698
  have eq94725 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq94705
  have eq94726 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq94725
  have eq94736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq412 y
       have i₂ := eq94726
       grind)
    | exact superpose eq94726 eq412
    | exact resolve eq412 eq94726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94726
  have eq94784 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq94736
       have r₂ := eq16
       grind)
    | exact resolve eq94736 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94736
  have eq94805 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq94784
       grind)
    | exact superpose eq94784 eq10
    | exact resolve eq10 eq94784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94784
  have eq95021 : x = (M.op y y) := by
    first
    | (have i₁ := eq94805
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq94805
    | exact resolve eq94805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94805
  have eq95044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq412 y
       have i₂ := eq95021
       grind)
    | exact superpose eq95021 eq412
    | exact resolve eq412 eq95021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq95021
  have eq95093 : False := by grind
  exact eq95093
